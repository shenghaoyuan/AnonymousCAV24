From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.arm Require Import ABinSem BinDecode.

From bpf.comm Require Import JITCall.
From bpf.rbpf32 Require Import JITConfig TSSyntax TSDecode Analyzer.
From bpf.jit Require Import ThumbJIT.

From Coq Require Import List ZArith Arith String Lia.
Import ListNotations.
Open Scope nat_scope.
Open Scope bool_scope.
Open Scope asm.

Fixpoint combiner_aux (kl: list (nat * bpf_code)) (base: nat): option (list (nat * (nat * bin_code))) :=
  match kl with
  | [] => Some []
  | (ep, l) :: tl =>
    match jit_alu32 l with
    | None => None
    | Some bl =>
      if Nat.ltb (base + List.length bl) JITTED_LIST_MAX_LENGTH then
        match combiner_aux tl (base + List.length bl) with
          (**r 4 * because of size_chunk Mint32 *)
        | None => None
        | Some cl =>  Some ((ep, (base, bl)) :: cl)
        end
      else
        None
    end
  end.

Definition combiner (kl: list (nat * bpf_code)): option (list (nat * (nat * bin_code))) :=
  combiner_aux kl 0.

Fixpoint concat_bin (l: list (nat * (nat * bin_code))): list (nat * nat) * bin_code :=
  match l with
  | [] => ([], [])
  | (ep, (ofs, bl)) :: tl => ((ep, ofs):: fst (concat_bin tl), bl ++ snd (concat_bin tl))
  end.

Definition whole_compiler (c: code): option (list (nat * nat) * bin_code) :=
  match analyzer c with
  | None => None
  | Some kl =>
    match kl with
    | [] => Some ([], []) (**r if rbpf doesn't have any alu32, returns [], or should be None? *)
    | _ =>
      match combiner kl with
      | None => None
      | Some bl => Some (concat_bin bl)
      end
    end
  end.

Fixpoint code_subset_in_blk (l: bin_code) (ofs: nat) (jit_blk: block) (m: mem): bool :=
  match l with
  | [] => true
  | hd :: tl =>
    match Mem.load Mint32 m jit_blk (Z.of_nat (4 * ofs)) with
    | None => false
    | Some v =>
      match v with
      | Vint i =>
        if Int.eq hd i then
          code_subset_in_blk tl (ofs+1) jit_blk m
        else
          false
      | _ => false
      end
    end
  end.

Lemma code_subset_in_blk_split:
  forall l1 l2 ofs jit_blk m,
    code_subset_in_blk (l1 ++ l2) ofs jit_blk m = true ->
      code_subset_in_blk l1 ofs jit_blk m = true /\
      code_subset_in_blk l2 (ofs + (List.length l1)) jit_blk m = true.
Proof.
  induction l1; simpl; intros; rename H into HL.
  - rewrite Nat.add_0_r.
    auto.
  - destruct Mem.load as [v | ]; [| inversion HL].
    destruct v; inversion HL.
    clear H0.
    rewrite HL.
    destruct Int.eq; [| inversion HL].
    eapply IHl1 in HL; eauto.
    destruct HL as (HL1 & HL2).
    split; [auto | ].
    replace (ofs + S (Datatypes.length l1))
      with (ofs + 1 + Datatypes.length l1) by lia.
    auto.
Qed.

(**r similar definition: bin_interp in ABinSem.v *)
Fixpoint exec_bin_list (l: bin_code) (ars: aregset) (astk: astack) (astkb: block) (m: mem): aoutcome :=
  if is_final_state ars then
    ANext ars astk astkb m
  else
    match l with
    | [] => ANext ars astk astkb m
    | hd :: tl =>
      match decode_thumb hd with
      | None => AStuck
      | Some arm_ins =>
        match aexec_instr true arm_ins ars astk astkb m with
        | AStuck => AStuck
        | ANext ars' astk' astkb' m' => exec_bin_list tl ars' astk' astkb' m'
        end
      end
  end.

Lemma exec_bin_list_split:
  forall  l1 l2 ars astk astkb m ars' astk' astkb' m'
    (EXE: exec_bin_list (l1 ++ l2) ars astk astkb m = ANext ars' astk' astkb' m'),
    exists ars1 astk1 astkb1 m1,
      exec_bin_list l1 ars astk astkb m = ANext ars1 astk1 astkb1 m1 /\
      exec_bin_list l2 ars1 astk1 astkb1 m1 = ANext ars' astk' astkb' m'.
Proof.
  induction l1; simpl; intros.
  - exists ars, astk, astkb, m.
    destruct is_final_state; split; auto.
  - destruct is_final_state eqn: Hfinal.
    + exists ars, astk, astkb, m.
      split;[reflexivity |].
      destruct l2.
      * simpl.
        destruct is_final_state; auto.
      * simpl.
        rewrite Hfinal.
        auto.
    + destruct decode_thumb as [arm_ins |]; [| inversion EXE].
      destruct aexec_instr as [ ars1 astk1 astkb1 m1 | ]; [| inversion EXE].
      eapply IHl1 in EXE.
      auto.
Qed.

Lemma exec_bin_list_concat:
  forall  l1 l2 ars astk astkb m ars1 astk1 astkb1 m1 ars' astk' astkb' m'
    (HE1: exec_bin_list l1 ars astk astkb m = ANext ars1 astk1 astkb1 m1)
    (HE2: exec_bin_list l2 ars1 astk1 astkb1 m1 = ANext ars' astk' astkb' m'),
      exec_bin_list (l1 ++ l2) ars astk astkb m = ANext ars' astk' astkb' m'.
Proof.
  induction l1; simpl; intros.
  - destruct is_final_state; inversion HE1; subst; auto.
  - destruct is_final_state eqn: Hfinal.
    + inversion HE1; subst.
      destruct l2.
      * simpl in HE2.
        rewrite Hfinal in HE2.
        auto.
      * simpl in HE2.
        rewrite Hfinal in HE2.
        auto.
    + destruct decode_thumb as [arm_ins |]; [| inversion HE1].
      destruct aexec_instr as [ ars_k astk_k astkb_k m_k | ]; [| inversion HE1].
      eapply IHl1; eauto.
Qed.

Definition code_subset_blk (l: bin_code) (ofs: nat) (jit_blk: block) (st: state): bool :=
  match st with
  | State _ m => code_subset_in_blk l 0 jit_blk m
  end.

Fixpoint compute_bin_ofs (bl: list (nat * (nat * bin_code))) (n o base: nat): bool :=
  match bl with
  | [] => false
  | (ep, (ofs, l)) :: tl =>
    match n with
    | O => (Nat.eqb ofs o) && (Nat.eqb ofs base)
    | S k => compute_bin_ofs tl k o (base + List.length l)
    end
  end.

Lemma combiner_aux_nth_error:
  forall kl n ep l bl base
    (IN: List.nth_error kl n = Some (ep, l))
    (HC : combiner_aux kl base = Some bl),
    exists ofs l1,
      List.nth_error bl n = Some (ep, (ofs, l1)) /\
      compute_bin_ofs bl n ofs base = true /\
      jit_alu32 l = Some l1 /\
      List.length l1 < JITTED_LIST_MAX_LENGTH /\
      ((Z.of_nat (ofs + Datatypes.length l1) * 4) < Int.max_unsigned)%Z.
Proof.
  induction kl; simpl; intros.
  - injection HC as Heq; subst bl.
    rewrite nth_error_nil in IN.
    inversion IN.
  - destruct n.
    + simpl in IN.
      injection IN as Heq; subst a.
      destruct jit_alu32 as [bl1 | ] eqn: HJIT; [| inversion HC].
      destruct ( _ <? _) eqn: HLE; [| inversion HC].
      destruct combiner_aux as [cl | ] eqn: Haux; [| inversion HC].
      injection HC as Heq.
      exists base, bl1.
      rewrite <- Heq.
      simpl.
      rewrite Nat.eqb_refl.
      rewrite Nat.ltb_lt in HLE.
      split; [auto| ].
      split; auto.
      split; auto.
      split; [lia |].
      unfold JITTED_LIST_MAX_LENGTH in HLE.
      change Int.max_unsigned with 4294967295%Z.
      lia.

    + simpl in IN.
      destruct a.
      destruct jit_alu32 as [bl1 | ] eqn: HJIT; [| inversion HC].
      destruct ( _ <? _) eqn: HLE; [| inversion HC].
      destruct combiner_aux as [cl | ] eqn: Haux; [| inversion HC].
      injection HC as Heq.
      eapply IHkl in Haux; eauto.
      destruct Haux as (ofs & l1 & HIN & Hofs & HJ).
      rewrite <- Heq.
      exists ofs, l1.
      split; simpl; auto.
Qed.

Lemma combiner_nth_error:
  forall kl n ep l bl
    (IN: List.nth_error kl n = Some (ep, l))
    (HC : combiner kl = Some bl),
    exists ofs l1,
      List.nth_error bl n = Some (ep, (ofs, l1)) /\
      compute_bin_ofs bl n ofs 0 = true /\
      jit_alu32 l = Some l1 /\
      List.length l1 < JITTED_LIST_MAX_LENGTH /\
      ((Z.of_nat (ofs + Datatypes.length l1) * 4) < Int.max_unsigned)%Z.
Proof.
  unfold combiner.
  intros.
  eapply combiner_aux_nth_error; eauto.
Qed.

Lemma nth_error_combiner:
  forall kl bl n v ofs l base
  (Hnth : nth_error bl n = Some (v, (ofs, l)))
  (Hcombiner : combiner_aux kl base = Some bl),
    exists l1,
    List.nth_error kl n = Some (v, l1).
Proof. 
  induction kl; simpl; intros.
  { inversion Hcombiner; subst.
    destruct n; simpl in Hnth; inversion Hnth.
  }

  destruct a as (ep1 & l1).
  destruct jit_alu32 as [bl1 | ] eqn: Halu32; [| inversion Hcombiner].
  destruct (_ <? _) eqn: HMAX; [| inversion Hcombiner].
  destruct combiner_aux as [cl1 |] eqn: Haux; inversion Hcombiner; subst.
  destruct n.
  { simpl in Hnth.
    inversion Hnth; subst.
    simpl.
    eexists; reflexivity.
  }

  simpl in Hnth.
  simpl.
  eapply IHkl; eauto.
Qed.

Lemma code_subset_in_blk_in:
  forall bl ofs jit_blk m n ep ofs1 l1 kv nbl
    (HC: concat_bin bl = (kv, nbl))
    (HSUB : code_subset_in_blk nbl ofs jit_blk m = true)
    (HOFS : compute_bin_ofs bl n ofs1 ofs = true)
    (HIN : nth_error bl n = Some (ep, (ofs1, l1))),
      code_subset_in_blk l1 ofs1 jit_blk m = true.
Proof.
  induction bl; simpl; intros.
  - rewrite nth_error_nil in HIN.
    inversion HIN.
  - destruct a as (ep_a, (ofs_a, l_a)).
    destruct n.
    + simpl in HIN.
      injection HIN as Heq; subst ep_a ofs_a l_a.
      apply andb_true_iff in HOFS.
      destruct HOFS as (_ & HOFS).
      apply beq_nat_true in HOFS.
      subst ofs1.
      injection HC as Hfst Hsnd.
      subst nbl.
      apply code_subset_in_blk_split in HSUB.
      destruct HSUB as (HSUB1 & HSUB2).
      auto.
    + simpl in HIN.
      injection HC as Hfst Hsnd.
      subst nbl.
      apply code_subset_in_blk_split in HSUB.
      destruct HSUB as (HSUB1 & HSUB2).
      eapply IHbl with (kv := fst (concat_bin bl)) in HSUB2; eauto.
      apply surjective_pairing.
Qed.

Lemma some_some_same:
  forall {A: Type} (x y: A),
    Some x = Some y ->
    x = y.
Proof.
  intros.
  injection H as Heq; auto.
Qed.