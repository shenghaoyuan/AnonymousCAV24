From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.arm Require Import ABinSem BinDecode.

From bpf.rbpf32 Require Import JITConfig TSSyntax TSDecode Analyzer.
From bpf.jit Require Import ThumbJIT WholeCompiler WholeCompilerGeneric WholeCompiler1.
From bpf.jit Require Import WholeCompiler2 ThumbJIT1 ListSetRefinement ThumbJIT1proof ListSetSort.

From Coq Require Import List ZArith Arith String Lia.
Import ListNotations.
Open Scope nat_scope.
Open Scope bool_scope.
Open Scope asm.

(**r use refined listset *)

Fixpoint get_alu32_jit_list_refine (c: code) (fuel pc counter: nat) (ld_set st_set: listset_regmap):
  option (bin_code * listset_regmap * listset_regmap * nat) :=
  match fuel with
  | O => None
  | S n =>
      match List.nth_error c pc with
      | None => None
      | Some ins =>
        match decode_ind ins with
        | None => None
        | Some bpf_ins =>
          match bpf_ins with
          | Palu32 op dst src =>
            match jit_one_refine op dst src ld_set st_set with
            | None => None
            | Some (l1, ld1, st1) =>
              match get_alu32_jit_list_refine c n (S pc) (S counter) ld1 st1 with
              | None => None
              | Some (l2, ld2, st2, counter2) => Some (l1 ++ l2, ld2, st2, counter2)
              end
            end
          | _ => Some ([], ld_set, st_set, counter)
          end
        end
      end
  end.

Definition compose_jit_list_aux_refine (c: code) (fuel pc counter: nat) (ld_set st_set: listset_regmap): option (bin_code * nat) :=
  match get_alu32_jit_list_refine c fuel pc counter ld_set st_set with
  | None => None
  | Some (bl, ld_set, st_set, n) =>
    match jit_alu32_thumb_pc n with
    | None => None
    | Some l_pc => Some (jit_alu32_pre ++ bl ++ l_pc ++
      (jit_alu32_thumb_store_refine st_set) ++
      (jit_alu32_thumb_reset_refine ld_set) ++ jit_alu32_post, n)
    end
  end.

Definition compose_jit_list_refine (c: code) (fuel pc: nat): option (bin_code * nat) :=
  compose_jit_list_aux_refine c fuel pc 0%nat init_listset_regmap init_listset_regmap.

Fixpoint whole_compiler3_aux (c: code) (fuel pc base: nat):
    option (list (nat * nat) * bin_code) :=
  match fuel with
  | O => Some ([], [])
  | S n =>
    if (Nat.eqb (List.length c) pc) then
      Some ([], [])
    else
    match find_instr pc c with
    | None => None
    | Some bpf_ins =>
      match bpf_ins with
      | Palu32 _ _ _ =>
        match compose_jit_list_refine c (List.length c - pc) pc with
        | None => None
        | Some (bl, len) =>
          match whole_compiler3_aux c n (pc + len) (base + (List.length bl)) with
          | None => None
          | Some (kv, l) => Some ((pc, base) :: kv, bl ++ l)
          end
        end

      | Pjmp ofs | Pjmpcmp _ _ _ ofs => (**r check if ins is jump *)
        let lbl := Z.to_nat (Int.signed
          (Int.add Int.one (Int.add (Int.repr (Z.of_nat pc)) ofs))) in
          match find_instr lbl c with
          | None => None
          | Some ins =>
            match ins with
            | Palu32 _ _ _ =>
              match compose_jit_list_refine c (List.length c - lbl) lbl with
              | None => None
              | Some (bl, _) =>
                match whole_compiler3_aux c n (S pc) (base + (List.length bl)) with
                | None => None
                | Some (kv, l) => Some ((lbl, base) :: kv, bl ++ l)
                end
              end
            | _ => whole_compiler3_aux c n (S pc) base
            end
          end
      | _ => (**r when ins is not jump *)
        whole_compiler3_aux c n (S pc) base
      end
    end
  end.

Definition whole_compiler3 (c: code):
    option (list (nat * nat) * bin_code) :=
  whole_compiler3_aux c (List.length c) 0%nat 0%nat.

Lemma get_alu32_jit_list_refine_eq:
  forall fuel pc c counter ld_set1 lr_ld1 st_set1 lr_st1 bl ld_set2 st_set2 n
  (Hnodup1: NoDup ld_set1)
  (Hnodup2: NoDup st_set1)
  (Hst1: eq_set_map ld_set1 lr_ld1)
  (Hst2: eq_set_map st_set1 lr_st1)
  (Hjit: get_alu32_jit_list c fuel pc counter ld_set1 st_set1 = Some (bl, ld_set2, st_set2, n)),
    exists lr_ld2 lr_st2,
      get_alu32_jit_list_refine c fuel pc counter lr_ld1 lr_st1 = Some (bl, lr_ld2, lr_st2, n) /\
    eq_set_map ld_set2 lr_ld2 /\
    eq_set_map st_set2 lr_st2 /\
    NoDup ld_set2 /\
    NoDup st_set2.
Proof.
  induction fuel; intros.
  { simpl in Hjit.
    inversion Hjit.
  }

  simpl in Hjit.
  simpl.
  destruct nth_error as [ins| ] eqn: Hnth; [| inversion Hjit].
  destruct decode_ind as [bpf_ins |] eqn: Hdecode; [| inversion Hjit].
  destruct bpf_ins; inversion Hjit; subst; try (
    eexists; eexists; split; [reflexivity | repeat (split; auto)]).
  clear H0.
  destruct jit_one as [((l1 & ld1) & st1) |] eqn: Hone; [| inversion Hjit].
  destruct get_alu32_jit_list as [(((l2 & ld2) & st2) & n2) |] eqn: Hget; [| inversion Hjit].
  eapply jit_one_refine_eq in Hone; eauto.
  destruct Hone as (lr_ld2 & lr_st2 & Hone & Heq1 & Heq2 & Hno1 & Hno2).
  rewrite Hone.
  eapply IHfuel in Hget; eauto.
  destruct Hget as (lr_ld3 & lr_st3 & Hget & Heq3 & Heq4 & Hno3 & Hno4).
  rewrite Hget.
  inversion Hjit; subst.
  eexists; eexists; split; [reflexivity |].
  repeat (split; auto).
Qed.

Lemma compose_jit_list_refine_eq:
  forall fuel pc c bl n,
    compose_jit_list c fuel pc = Some (bl, n) ->
      compose_jit_list_refine c fuel pc = Some (bl, n).
Proof.
  unfold compose_jit_list_refine, compose_jit_list,
    compose_jit_list_aux, compose_jit_list_aux_refine; intros.
  destruct get_alu32_jit_list as [(((tl & ld_set) & st_set) & k) |] eqn: Hget; [| inversion H].
  assert (Heq_nil: eq_set_map [] init_listset_regmap). {
    unfold eq_set_map, init_listset_regmap.
    intros.
    split; intro HF.
    - inversion HF.
    - destruct r; simpl in HF; inversion HF.
  }
  eapply get_alu32_jit_list_refine_eq in Hget; eauto; try (apply NoDup_nil).
  destruct Hget as (lr_ld2 & lr_st2 & Hget & Heq1 & Heq2 & Hno1 & Hno2).
  rewrite Hget.
  destruct jit_alu32_thumb_pc as [l_pc |]; [| inversion H].
  rewrite <- H.
  apply eq_set_map_sort_list_same in Heq1.
  apply eq_set_map_sort_list_same in Heq2.
  repeat f_equal.
  - erewrite jit_alu32_thumb_store_refine_eq with (st_set := sort_listset st_set); eauto.
    + apply NoDup_sort_listset; auto.
    + apply sort_sort_listset.
  - erewrite jit_alu32_thumb_reset_refine_eq with (ld_set := sort_listset ld_set); eauto.
    + apply NoDup_sort_listset; auto.
    + apply sort_sort_listset.
Qed.

Lemma whole_compiler3_aux_same:
  forall fuel c pc base kv l,
    whole_compiler2_aux c fuel pc base = Some (kv, l) ->
    whole_compiler3_aux c fuel pc base = Some (kv, l).
Proof.
  induction fuel; simpl; intros c pc base kv l Haux.
  { auto. }

  destruct (_ =? _) eqn: Heq_len.
  { auto. }

  destruct find_instr as [ins|] eqn: Hfind; [| inversion Haux].
  destruct ins; try (eapply IHfuel; eauto; lia).
  - destruct compose_jit_list as [(l1 & len )|] eqn: HL1; [| inversion Haux].
    erewrite compose_jit_list_refine_eq; eauto.

    destruct whole_compiler2_aux as [(kvk, lk)|] eqn: Hauxk in Haux;[| inversion Haux].
    erewrite IHfuel; eauto.

  - destruct find_instr as [ins_pc|] eqn: Hfind1 in Haux; [| inversion Haux].
    rewrite Hfind1.
    destruct ins_pc; try (eapply IHfuel; eauto; lia).

    destruct compose_jit_list as [(l1 & len )|] eqn: HL1; [| inversion Haux].
    erewrite compose_jit_list_refine_eq; eauto.

    destruct whole_compiler2_aux as [(kvk, lk)|] eqn: Hauxk in Haux;[| inversion Haux].
    erewrite IHfuel; eauto.

  - destruct find_instr as [ins_pc|] eqn: Hfind1 in Haux; [| inversion Haux].
    rewrite Hfind1.
    destruct ins_pc; try (eapply IHfuel; eauto; lia).

    destruct compose_jit_list as [(l1 & len )|] eqn: HL1; [| inversion Haux].
    erewrite compose_jit_list_refine_eq; eauto.

    destruct whole_compiler2_aux as [(kvk, lk)|] eqn: Hauxk in Haux;[| inversion Haux].
    erewrite IHfuel; eauto.
Qed.

Theorem whole_compiler3_same:
  forall c kv l,
    whole_compiler2 c = Some (kv, l) ->
    whole_compiler3 c = Some (kv, l).
Proof.
  unfold whole_compiler2, whole_compiler3; intros.
  eapply whole_compiler3_aux_same; eauto.
Qed.