From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.arm Require Import ABinSem BinDecode.

From bpf.rbpf32 Require Import JITConfig TSSyntax TSDecode Analyzer.
From bpf.jit Require Import ThumbJIT WholeCompiler WholeCompilerGeneric WholeCompiler1 ListSetSort.

From Coq Require Import List ZArith Arith String Lia.
Import ListNotations.
Open Scope nat_scope.
Open Scope bool_scope.
Open Scope asm.

(**r get a list of alu32 then jit a list of alu32 jit_alu32
      ->
      get one alu32 then jit_one alu32 *)

Fixpoint get_alu32_jit_list (c: code) (fuel pc counter: nat) (ld_set st_set: listset):
  option (bin_code * listset * listset * nat) :=
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
            match jit_one op dst src ld_set st_set with
            | None => None
            | Some (l1, ld1, st1) =>
              match get_alu32_jit_list c n (S pc) (S counter) ld1 st1 with
              | None => None
              | Some (l2, ld2, st2, counter2) => Some (l1 ++ l2, ld2, st2, counter2)
              end
            end
          | _ => Some ([], ld_set, st_set, counter)
          end
        end
      end
  end.

Definition compose_jit_list_aux (c: code) (fuel pc counter: nat) (ld_set st_set: listset): option (bin_code * nat) :=
  match get_alu32_jit_list c fuel pc counter ld_set st_set with
  | None => None
  | Some (bl, ld_set, st_set, n) =>
    match jit_alu32_thumb_pc n with
    | None => None
    | Some l_pc => Some (jit_alu32_pre ++ bl ++ l_pc ++
      (jit_alu32_thumb_store (sort_listset st_set)) ++
      (jit_alu32_thumb_reset (sort_listset ld_set)) ++ jit_alu32_post, n)
    end
  end.

Definition compose_jit_list (c: code) (fuel pc: nat): option (bin_code * nat) :=
  compose_jit_list_aux c fuel pc 0%nat [] [].

Fixpoint whole_compiler2_aux (c: code) (fuel pc base: nat):
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
        match compose_jit_list c (List.length c - pc) pc with
        | None => None
        | Some (bl, len) =>
          match whole_compiler2_aux c n (pc + len) (base + (List.length bl)) with
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
              match compose_jit_list c (List.length c - lbl) lbl with
              | None => None
              | Some (bl, _) =>
                match whole_compiler2_aux c n (S pc) (base + (List.length bl)) with
                | None => None
                | Some (kv, l) => Some ((lbl, base) :: kv, bl ++ l)
                end
              end
            | _ => whole_compiler2_aux c n (S pc) base
            end
          end
      | _ => (**r when ins is not jump *)
        whole_compiler2_aux c n (S pc) base
      end
    end
  end.

Definition whole_compiler2 (c: code):
    option (list (nat * nat) * bin_code) :=
  whole_compiler2_aux c (List.length c) 0%nat 0%nat.

Lemma get_alu32_list_jit_list:
  forall pc c l1 bl counter ld1 st1 ld2 st2,
    get_alu32_list c pc (Datatypes.length c - pc) = Some l1 ->
    pc <= List.length c ->
    jit_sequence l1 ld1 st1 = Some (bl, ld2, st2) ->
      get_alu32_jit_list c pc (Datatypes.length c - pc) counter ld1 st1 =
      Some (bl, ld2, st2, List.length l1+counter).
Proof.
  induction pc; intros c l1 bl counter ld1 st1 ld2 st2 Hget HLE Hjit.
  { inversion Hget. }

  simpl in Hget.
  simpl get_alu32_jit_list at 1.
  destruct nth_error as [ins| ] eqn: Hnth; [| inversion Hget].
  destruct decode_ind as [bpf_ins |] eqn: Hdecode; [| inversion Hget].
  unfold is_alu32 in Hget.
  destruct bpf_ins; try (injection Hget as Heq; subst l1;
    unfold jit_alu32 in Hjit;
    simpl in Hjit;
    inversion Hjit; simpl; f_equal).
  rename a into op; rename b into dst; rename s into src.
  replace (S (Datatypes.length c - S pc))%nat with (Datatypes.length c - pc)%nat in * by lia.

  destruct get_alu32_list as [tl|] eqn: Hget_alu32; [|inversion Hget].
  injection Hget as Hl1_eq; subst l1.

  simpl jit_sequence at 1 in Hjit.
  destruct jit_one as [((l3, ld3), st3) |] eqn: Hone; [| inversion Hjit].
  destruct jit_sequence as [((l4, ld4), st4) |] eqn: Hseq; [| inversion Hjit].
  injection Hjit as Hbl_eq Hld2_eq Hst2_eq; subst bl ld2 st2.

  specialize (IHpc c tl l4 (S counter) ld3 st3 ld4 st4 Hget_alu32).
  assert (Heq: pc <= Datatypes.length c) by lia.
  specialize (IHpc Heq); clear Heq.
  specialize (IHpc Hseq).

  destruct get_alu32_jit_list as [(((l5, ld5), st5), n5)|] eqn: HList; [| inversion IHpc].
  injection IHpc as Hl5_eq Hld5_eq Hst5_eq Hn5_eq; subst.
  simpl. rewrite Nat.add_succ_r.
  f_equal.
Qed.

Lemma get_alu32_list_jit_alu32_generic_compose:
  forall pc c l1 bl,
    get_alu32_list c pc (Datatypes.length c - pc) = Some l1 ->
    pc <= List.length c ->
    jit_alu32_generic l1 = Some bl ->
      compose_jit_list c pc (Datatypes.length c - pc) =
      Some (bl, List.length l1).
Proof.
  unfold jit_alu32_generic, compose_jit_list.
  unfold jit_alu32_generic_aux, compose_jit_list_aux; intros.
  destruct jit_sequence as [((cl, ld_set), st_set) |] eqn: Hseq; [| inversion H1].
  destruct cl as [| chd ctl] eqn: HCL; [inversion H1|].
  rewrite <- HCL in *.
  eapply get_alu32_list_jit_list with (counter := 0) in Hseq; eauto.
  rewrite Hseq.
  rewrite Nat.add_0_r.
  destruct jit_alu32_thumb_pc as [l_pc |]; [| inversion H1].
  apply some_some_same in H1.
  rewrite H1.
  f_equal.
Qed.

Lemma whole_compiler2_aux_same:
  forall fuel c pc base kv l,
    fuel <= List.length c ->
    whole_compiler1_aux c fuel pc base = Some (kv, l) ->
    whole_compiler2_aux c fuel pc base = Some (kv, l).
Proof.
  induction fuel; simpl; intros c pc base kv l HLE Haux.
  { auto. }

  destruct (_ =? _) eqn: Heq_len.
  { auto. }

  destruct find_instr as [ins|] eqn: Hfind; [| inversion Haux].
  destruct ins; try (eapply IHfuel; eauto; lia).
  - destruct get_alu32_list as [l1|] eqn: HL1; [| inversion Haux].
    destruct jit_alu32_generic as [ bl | ] eqn: Hg; [| inversion Haux].
    assert (Hle: pc < List.length c). {
      clear - Hfind.
      unfold find_instr in Hfind.
      destruct nth_error eqn: Hnth; [| inversion Hfind].
      eapply nth_error_Some; eauto.
      rewrite Hnth. intro HF; inversion HF.
    }
    remember (Datatypes.length c - pc) as n eqn: Hneq.
    assert (Heq: pc = (Datatypes.length c - n)) by lia.
    subst pc.
    eapply get_alu32_list_jit_alu32_generic_compose in HL1; eauto.
    2:{ lia. }
    rewrite HL1.

    destruct whole_compiler1_aux as [(kvk, lk)|] eqn: Hauxk in Haux;[| inversion Haux].
    erewrite IHfuel; eauto. lia.

  - destruct find_instr as [ins_pc|] eqn: Hfind1 in Haux; [| inversion Haux].
    rewrite Hfind1.
    destruct ins_pc; try (eapply IHfuel; eauto; lia).

    destruct get_alu32_list as [l1|] eqn: HL1; [| inversion Haux].
    destruct jit_alu32_generic as [ bl | ] eqn: Hg; [| inversion Haux].
    remember (Z.to_nat (Int.signed (Int.add Int.one (Int.add (Int.repr (Z.of_nat pc)) o)))) as ofs eqn: Hofs.
    assert (Hle: ofs < List.length c). {
      clear - Hofs Hfind1.
      unfold find_instr in Hfind1.
      destruct nth_error eqn: Hnth; [| inversion Hfind1].
      eapply nth_error_Some; eauto.
      rewrite Hnth. intro HF; inversion HF.
    }
    remember (Datatypes.length c - ofs) as n eqn: Hneq.
    assert (Heq: ofs = (Datatypes.length c - n)) by lia.
    rewrite Heq in *; clear Heq.
    eapply get_alu32_list_jit_alu32_generic_compose in HL1; eauto.
    2:{ lia. }
    rewrite HL1.

    destruct whole_compiler1_aux as [(kvk, lk)|] eqn: Hauxk in Haux;[| inversion Haux].
    erewrite IHfuel; eauto. lia.

  - destruct find_instr as [ins_pc|] eqn: Hfind1 in Haux; [| inversion Haux].
    rewrite Hfind1.
    destruct ins_pc; try (eapply IHfuel; eauto; lia).

    destruct get_alu32_list as [l1|] eqn: HL1; [| inversion Haux].
    destruct jit_alu32_generic as [ bl | ] eqn: Hg; [| inversion Haux].
    remember (Z.to_nat (Int.signed (Int.add Int.one (Int.add (Int.repr (Z.of_nat pc)) o)))) as ofs eqn: Hofs.
    assert (Hle: ofs < List.length c). {
      clear - Hofs Hfind1.
      unfold find_instr in Hfind1.
      destruct nth_error eqn: Hnth; [| inversion Hfind1].
      eapply nth_error_Some; eauto.
      rewrite Hnth. intro HF; inversion HF.
    }
    remember (Datatypes.length c - ofs) as n eqn: Hneq.
    assert (Heq: ofs = (Datatypes.length c - n)) by lia.
    rewrite Heq in *; clear Heq.
    eapply get_alu32_list_jit_alu32_generic_compose in HL1; eauto.
    2:{ lia. }
    rewrite HL1.

    destruct whole_compiler1_aux as [(kvk, lk)|] eqn: Hauxk in Haux;[| inversion Haux].
    erewrite IHfuel; eauto. lia.
Qed.

Theorem whole_compiler2_same:
  forall c kv l,
    whole_compiler1 c = Some (kv, l) ->
    whole_compiler2 c = Some (kv, l).
Proof.
  unfold whole_compiler1, whole_compiler2; intros.
  eapply whole_compiler2_aux_same; eauto.
Qed.