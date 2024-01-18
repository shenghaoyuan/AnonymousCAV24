From compcert Require Import Integers.
From compcert.arm Require Import AsmSyntax BinSyntax BinDecode.

From bpf.comm Require Import Flag BinrBPF ListAsArray Regs LemmaInt.
From bpf.rbpf32 Require Import TSSyntax TSDecode JITConfig.
From bpf.jit Require Import Arm32Reg ThumbInsOp ListSetRefinement ThumbJIT ThumbJIT1 ThumbJITLtac ListSetSort.

From Coq Require Import List ZArith Arith String ListSet Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope asm.

Definition eq_set_map (l: listset) (lr: listset_regmap): Prop :=
  forall r,
    (List.In r l <-> eval_listset_regmap r lr = true).

Lemma eq_set_map_sort_list_same:
  forall l lr
    (Hst: eq_set_map l lr),
    eq_set_map (sort_listset l) lr.
Proof.
  unfold eq_set_map; intros.
  split; intro HF.
  - apply Hst.
    apply In_sort_listset_intro1; auto.
  - apply In_sort_listset_intro2; auto.
    apply Hst; auto.
Qed.

Lemma add_eq_set_map:
  forall l r lr
    (Hst: eq_set_map l lr),
    set_mem breg_eq r l = eval_listset_regmap r lr.
Proof.
  unfold eq_set_map; simpl; intros.
  specialize (Hst r).
  destruct (eval_listset_regmap).
  - apply set_mem_correct2.
    unfold set_In.
    apply Hst.
    auto.
  - apply set_mem_complete2.
    unfold set_In.
    intro HF.
    destruct Hst as (Hst & _).
    specialize (Hst HF).
    inversion Hst.
Qed.

Lemma ireg_of_breg_int_eq:
  forall r, int_of_breg r = int_of_ireg (ireg_of_breg r).
Proof.
  unfold int_of_breg, int_of_ireg; destruct r; simpl; intros; reflexivity.
Qed.

Lemma breg_not_in_rbpf_arm_callee_save:
  forall r, ~ set_In r rbpf_arm_callee_save -> In r [R0; R1; R2; R3].
Proof.
  unfold set_In; simpl; intros.
  destruct r.
  - left; auto.
  - right; left; auto.
  - do 2 right; left; auto.
  - do 3 right; left; auto.
  - exfalso; apply H; left; auto.
  - exfalso; apply H; right; left; auto.
  - exfalso; apply H; do 2 right; left; auto.
  - exfalso; apply H; do 3 right; left; auto.
  - exfalso; apply H; do 4 right; left; auto.
  - exfalso; apply H; do 5 right; left; auto.
  - exfalso; apply H; do 6 right; left; auto.
Qed.

Lemma rbpf_arm_callee_save_range:
  forall r,
  set_mem breg_eq r rbpf_arm_callee_save =
  Int.ltu (Int.repr 3) (int_of_breg r) && Int.ltu (int_of_breg r) (int_of_ireg IR12).
Proof.
  intros.
  symmetry.
  rewrite ireg_of_breg_int_eq.
  destruct set_mem eqn: Hset_mem.
  - apply Bool.andb_true_iff.
    rewrite ! Clt_Zlt_unsigned.
    replace (Int.unsigned (Int.repr 3)) with 3%Z by reflexivity.
    replace (Int.unsigned (int_of_ireg IR12)) with 12%Z by reflexivity.
    apply set_mem_correct1 in Hset_mem.
    unfold set_In in Hset_mem.
    simpl in Hset_mem.
    unfold int_of_ireg.
    repeat (destruct Hset_mem as [Hset_mem | Hset_mem];
    [rewrite <- Hset_mem; simpl; prove_int|]).
    inversion Hset_mem.
  - apply set_mem_complete1 in Hset_mem.
    apply breg_not_in_rbpf_arm_callee_save in Hset_mem.
    simpl in Hset_mem.
    apply Bool.andb_false_iff.
    left.
    apply Bool.negb_true_iff.
    apply Cle_Zle_unsigned.
    replace (Int.unsigned (Int.repr 3)) with 3%Z by reflexivity.
    unfold int_of_ireg.
    repeat (destruct Hset_mem as [Hset_mem | Hset_mem];
    [rewrite <- Hset_mem; simpl; prove_int|]).
    inversion Hset_mem.
Qed.

Lemma jit_call_save_add_refine_eq:
  forall l lr r bl
  (Hst: eq_set_map l lr)
  (Hjit: jit_call_save_add r l = bl),
    jit_call_save_add_refine r lr = bl.
Proof.
  unfold jit_call_save_add, jit_call_save_add_refine; intros.
  erewrite <- add_eq_set_map; eauto.
  destruct set_mem eqn: Hset_mem; [assumption |].
  rewrite <- rbpf_arm_callee_save_range. assumption.
Qed.

Lemma set_add_refine_eq:
  forall l lr dst,
  eq_set_map l lr -> eq_set_map (set_add breg_eq dst l) (listset_add_regmap dst lr).
Proof.
  unfold eq_set_map; intros.
  specialize (H r).
  destruct H as (HL & HR).

  destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
  - subst r.
    split; intro HT.
    + apply eval_upd_listset_regmap.
    + apply set_add_intro2; auto.
  - split; intro HT.
    + rewrite eval_upd_listset_regmap_other; auto.
      apply HL.
      apply set_add_elim in HT.
      destruct HT as [HF | HT]; [exfalso; apply Hr_neq; auto | ].
      unfold set_In in HT; auto.
    + rewrite eval_upd_listset_regmap_other in HT; auto.
      specialize (HR HT).
      apply set_add_intro1; auto.
Qed.

Lemma jit_call_save_reg_refine_eq:
  forall ld_set1 lr_ld1 st_set1 lr_st1 dst src bl ld_set2 st_set2
  (Hnodup1: NoDup ld_set1)
  (Hnodup2: NoDup st_set1)
  (Hst1: eq_set_map ld_set1 lr_ld1)
  (Hst2: eq_set_map st_set1 lr_st1)
  (Hjit: jit_call_save_reg dst src ld_set1 st_set1 = (bl, ld_set2, st_set2)),
    exists lr_ld2 lr_st2,
    jit_call_save_reg_refine dst src lr_ld1 lr_st1 = (bl, lr_ld2, lr_st2) /\
    eq_set_map ld_set2 lr_ld2 /\
    eq_set_map st_set2 lr_st2 /\
    NoDup ld_set2 /\
    NoDup st_set2.
Proof.
  unfold jit_call_save_reg, jit_call_save_reg_refine; intros.
  erewrite jit_call_save_add_refine_eq; eauto.
  eapply set_add_refine_eq with (dst := dst) in Hst1 as Hst3.
  erewrite jit_call_save_add_refine_eq; eauto.
  injection Hjit as Hbl_eq Hld2_eq Hst2_eq.
  subst.
  eexists; eexists.
  split; eauto.
  split; [apply set_add_refine_eq; auto | ].
  split; [apply set_add_refine_eq; auto | ].
  split; repeat apply set_add_nodup; auto.
Qed.

Lemma jit_call_save_imm_refine_eq:
  forall ld_set1 lr_ld1 st_set1 lr_st1 dst bl ld_set2 st_set2
  (Hnodup1: NoDup ld_set1)
  (Hnodup2: NoDup st_set1)
  (Hst1: eq_set_map ld_set1 lr_ld1)
  (Hst2: eq_set_map st_set1 lr_st1)
  (Hjit: jit_call_save_imm dst ld_set1 st_set1 = (bl, ld_set2, st_set2)),
    exists lr_ld2 lr_st2,
      jit_call_save_imm_refine dst lr_ld1 lr_st1 = (bl, lr_ld2, lr_st2) /\
    eq_set_map ld_set2 lr_ld2 /\
    eq_set_map st_set2 lr_st2 /\
    NoDup ld_set2 /\
    NoDup st_set2.
Proof.
  unfold jit_call_save_imm, jit_call_save_imm_refine; intros.
  erewrite jit_call_save_add_refine_eq; eauto.
  injection Hjit as Hbl_eq Hld2_eq Hst2_eq.
  subst.
  eexists; eexists.
  split; eauto.
  split; [apply set_add_refine_eq; auto | ].
  split; [apply set_add_refine_eq; auto | ].
  split; repeat apply set_add_nodup; auto.
Qed.

Lemma jit_one_refine_eq:
  forall ld_set1 lr_ld1 st_set1 lr_st1 op dst src bl ld_set2 st_set2
  (Hnodup1: NoDup ld_set1)
  (Hnodup2: NoDup st_set1)
  (Hst1: eq_set_map ld_set1 lr_ld1)
  (Hst2: eq_set_map st_set1 lr_st1)
  (Hjit: jit_one op dst src ld_set1 st_set1 = Some (bl, ld_set2, st_set2)),
    exists lr_ld2 lr_st2,
      jit_one_refine op dst src lr_ld1 lr_st1 = Some (bl, lr_ld2, lr_st2) /\
    eq_set_map ld_set2 lr_ld2 /\
    eq_set_map st_set2 lr_st2 /\
    NoDup ld_set2 /\
    NoDup st_set2.
Proof.
  unfold jit_one, jit_one_refine; intros.
  destruct src.
  - destruct jit_call_save_reg as ((l1 & ld_set1_1) & st_set1_1) eqn: Hreg_eq.
    destruct jit_call_save_reg_refine as ((lr1 & lr_ld1_1) & lr_st1_1) eqn: Hreg_eq1.
    destruct bpf_alu32_to_thumb_reg as [l2 |] eqn: Hreg; [| inversion Hjit].
    inversion Hjit; subst; clear Hjit.
    eapply jit_call_save_reg_refine_eq in Hreg_eq; eauto.
    destruct Hreg_eq as (lr_ld2 & lr_st2 & Hreg_eq & Heq1 & Heq2).
    rewrite Hreg_eq1 in Hreg_eq.
    inversion Hreg_eq; subst; clear Hreg_eq.
    eexists; eexists. split; eauto.
  - destruct jit_call_save_imm as ((l1 & ld_set1_1) & st_set1_1) eqn: Hreg_eq.
    destruct jit_call_save_imm_refine as ((lr1 & lr_ld1_1) & lr_st1_1) eqn: Hreg_eq1.
    destruct bpf_alu32_to_thumb_imm as [l2 |] eqn: Hreg; [| inversion Hjit].
    inversion Hjit; subst; clear Hjit.
    eapply jit_call_save_imm_refine_eq in Hreg_eq; eauto.
    destruct Hreg_eq as (lr_ld2 & lr_st2 & Hreg_eq & Heq1 & Heq2).
    rewrite Hreg_eq1 in Hreg_eq.
    inversion Hreg_eq; subst; clear Hreg_eq.
    eexists; eexists. split; eauto.
Qed.

Lemma jit_sequence_refine_eq:
  forall l ld_set1 lr_ld1 st_set1 lr_st1 bl ld_set2 st_set2
  (Hnodup1: NoDup ld_set1)
  (Hnodup2: NoDup st_set1)
  (Hst1: eq_set_map ld_set1 lr_ld1)
  (Hst2: eq_set_map st_set1 lr_st1)
  (Hjit: jit_sequence l ld_set1 st_set1 = Some (bl, ld_set2, st_set2)),
    exists lr_ld2 lr_st2,
      jit_sequence_refine l lr_ld1 lr_st1 = Some (bl, lr_ld2, lr_st2) /\
    eq_set_map ld_set2 lr_ld2 /\
    eq_set_map st_set2 lr_st2 /\
    NoDup ld_set2 /\
    NoDup st_set2.
Proof.
  induction l; simpl; intros.
  { inversion Hjit; subst; clear Hjit.
    eexists; eexists; split; eauto.
  }

  destruct a; inversion Hjit. clear H0.
  rename a into op; rename b into dst; rename s into src.
  destruct jit_one as [((l1 & ld_set1_1) & st_set1_1) |] eqn: Hone; [| inversion Hjit].
  destruct jit_sequence as [((l2 & ld_set2_1) & st_set2_1) |] eqn: Hseq; [| inversion Hjit].
  eapply jit_one_refine_eq in Hone; eauto.
  destruct Hone as (lr_ld2 & lr_st2 & Hone & Heq1 & Heq2 & Hno1 & Hno2).
  rewrite Hone.
  eapply IHl in Hseq; eauto.
  destruct Hseq as (lr_ld3 & lr_st3 & Hseq & Heq3 & Heq4 & Hno3 & Hno4).
  rewrite Hseq.
  inversion Hjit; subst; clear Hjit.
  eexists; eexists; split; eauto.
Qed.

Lemma jit_alu32_thumb_upd_store_reset_same:
  forall r lr_st,
  jit_alu32_thumb_upd_store r (reset_listset_regmap r lr_st) = [].
Proof.
  intros.
  unfold jit_alu32_thumb_upd_store.
  rewrite eval_listset_regmap_reset_listset_regmap_same.
  reflexivity.
Qed.

Lemma jit_alu32_thumb_upd_store_reset_other:
  forall r r' lr_st,
  r <> r' ->
  jit_alu32_thumb_upd_store r (reset_listset_regmap r' lr_st) = jit_alu32_thumb_upd_store r lr_st.
Proof.
  intros.
  unfold jit_alu32_thumb_upd_store.
  rewrite eval_listset_regmap_reset_listset_regmap_other; auto.
Qed.

Lemma my_app_tail: forall [A : Type] (l l1 l2 : list A), l1 = l2 -> l1 ++ l = l2 ++ l.
Proof.
  intros.
  subst l1.
  reflexivity.
Qed.

Lemma my_app_hd: forall [A : Type] (l : list A) a, a :: l = [a] ++ l.
Proof.
  intros.
  simpl.
  auto.
Qed.

Ltac list_store_solver X lr_st H :=
  match goal with
  | |- _ =>
    assert (Heq: jit_alu32_thumb_upd_store X lr_st = []) by
    (unfold jit_alu32_thumb_upd_store; rewrite H; auto);
    rewrite Heq in *; clear Heq
  end.


Lemma jit_alu32_thumb_store_refine_reset:
  forall a lr_st tl bl
  (Hlt_a_false : forall r : breg,
              (z_of_breg a <=? z_of_breg r) = false -> eval_listset_regmap r lr_st = false)
  (Htl: jit_alu32_thumb_store_refine (reset_listset_regmap a lr_st) = tl)
  (Hjit : [jit_alu32_thumb_mem_template_jit STR_I_OP (int_of_breg a) (int_of_ireg IR12)
           (Int.mul (int_of_breg a) (Int.repr 4))] ++ tl = bl)
  (Heq_a_true : eval_listset_regmap a lr_st = true),
    jit_alu32_thumb_store_refine lr_st = bl.
Proof.
  unfold jit_alu32_thumb_store_refine; intros.
  destruct (breg_eq R0 a) as [Hr0_eq | Hr0_neq].
  { subst a.
    rewrite jit_alu32_thumb_upd_store_reset_same in Htl.
    do 10 (rewrite jit_alu32_thumb_upd_store_reset_other in Htl; [| intro HF; inversion HF]).
    rewrite app_nil_l in Htl.
    rewrite <- Hjit.
    rewrite <- Htl.
    apply my_app_tail.
    unfold jit_alu32_thumb_upd_store.
    rewrite Heq_a_true; auto.
  }
  destruct (breg_eq R1 a) as [Hr1_eq | Hr1_neq].
  { subst a.
    rewrite jit_alu32_thumb_upd_store_reset_same in Htl.
    do 10 (rewrite jit_alu32_thumb_upd_store_reset_other in Htl; [| intro HF; inversion HF]).
    list_store_solver R0 lr_st Hlt_a_false.
    rewrite ! app_nil_l in *.
    rewrite <- Hjit.
    rewrite <- Htl.
    apply my_app_tail.
    unfold jit_alu32_thumb_upd_store.
    rewrite Heq_a_true; auto.
  }

  destruct (breg_eq R2 a) as [Hr2_eq | Hr2_neq].
  { subst a.
    rewrite jit_alu32_thumb_upd_store_reset_same in Htl.
    do 10 (rewrite jit_alu32_thumb_upd_store_reset_other in Htl; [| intro HF; inversion HF]).
    list_store_solver R0 lr_st Hlt_a_false.
    list_store_solver R1 lr_st Hlt_a_false.
    rewrite ! app_nil_l in *.
    rewrite <- Hjit.
    rewrite <- Htl.
    apply my_app_tail.
    unfold jit_alu32_thumb_upd_store.
    rewrite Heq_a_true; auto.
  }

  destruct (breg_eq R3 a) as [Hr3_eq | Hr3_neq].
  { subst a.
    rewrite jit_alu32_thumb_upd_store_reset_same in Htl.
    do 10 (rewrite jit_alu32_thumb_upd_store_reset_other in Htl; [| intro HF; inversion HF]).
    list_store_solver R0 lr_st Hlt_a_false.
    list_store_solver R1 lr_st Hlt_a_false.
    list_store_solver R2 lr_st Hlt_a_false.
    rewrite ! app_nil_l in *.
    rewrite <- Hjit.
    rewrite <- Htl.
    apply my_app_tail.
    unfold jit_alu32_thumb_upd_store.
    rewrite Heq_a_true; auto.
  }

  destruct (breg_eq R4 a) as [Hr4_eq | Hr4_neq].
  { subst a.
    rewrite jit_alu32_thumb_upd_store_reset_same in Htl.
    do 10 (rewrite jit_alu32_thumb_upd_store_reset_other in Htl; [| intro HF; inversion HF]).
    list_store_solver R0 lr_st Hlt_a_false.
    list_store_solver R1 lr_st Hlt_a_false.
    list_store_solver R2 lr_st Hlt_a_false.
    list_store_solver R3 lr_st Hlt_a_false.
    rewrite ! app_nil_l in *.
    rewrite <- Hjit.
    rewrite <- Htl.
    apply my_app_tail.
    unfold jit_alu32_thumb_upd_store.
    rewrite Heq_a_true; auto.
  }

  destruct (breg_eq R5 a) as [Hr5_eq | Hr5_neq].
  { subst a.
    rewrite jit_alu32_thumb_upd_store_reset_same in Htl.
    do 10 (rewrite jit_alu32_thumb_upd_store_reset_other in Htl; [| intro HF; inversion HF]).
    list_store_solver R0 lr_st Hlt_a_false.
    list_store_solver R1 lr_st Hlt_a_false.
    list_store_solver R2 lr_st Hlt_a_false.
    list_store_solver R3 lr_st Hlt_a_false.
    list_store_solver R4 lr_st Hlt_a_false.
    rewrite ! app_nil_l in *.
    rewrite <- Hjit.
    rewrite <- Htl.
    apply my_app_tail.
    unfold jit_alu32_thumb_upd_store.
    rewrite Heq_a_true; auto.
  }

  destruct (breg_eq R6 a) as [Hr6_eq | Hr6_neq].
  { subst a.
    rewrite jit_alu32_thumb_upd_store_reset_same in Htl.
    do 10 (rewrite jit_alu32_thumb_upd_store_reset_other in Htl; [| intro HF; inversion HF]).
    list_store_solver R0 lr_st Hlt_a_false.
    list_store_solver R1 lr_st Hlt_a_false.
    list_store_solver R2 lr_st Hlt_a_false.
    list_store_solver R3 lr_st Hlt_a_false.
    list_store_solver R4 lr_st Hlt_a_false.
    list_store_solver R5 lr_st Hlt_a_false.
    rewrite ! app_nil_l in *.
    rewrite <- Hjit.
    rewrite <- Htl.
    apply my_app_tail.
    unfold jit_alu32_thumb_upd_store.
    rewrite Heq_a_true; auto.
  }

  destruct (breg_eq R7 a) as [Hr7_eq | Hr7_neq].
  { subst a.
    rewrite jit_alu32_thumb_upd_store_reset_same in Htl.
    do 10 (rewrite jit_alu32_thumb_upd_store_reset_other in Htl; [| intro HF; inversion HF]).
    list_store_solver R0 lr_st Hlt_a_false.
    list_store_solver R1 lr_st Hlt_a_false.
    list_store_solver R2 lr_st Hlt_a_false.
    list_store_solver R3 lr_st Hlt_a_false.
    list_store_solver R4 lr_st Hlt_a_false.
    list_store_solver R5 lr_st Hlt_a_false.
    list_store_solver R6 lr_st Hlt_a_false.
    rewrite ! app_nil_l in *.
    rewrite <- Hjit.
    rewrite <- Htl.
    apply my_app_tail.
    unfold jit_alu32_thumb_upd_store.
    rewrite Heq_a_true; auto.
  }

  destruct (breg_eq R8 a) as [Hr8_eq | Hr8_neq].
  { subst a.
    rewrite jit_alu32_thumb_upd_store_reset_same in Htl.
    do 10 (rewrite jit_alu32_thumb_upd_store_reset_other in Htl; [| intro HF; inversion HF]).
    list_store_solver R0 lr_st Hlt_a_false.
    list_store_solver R1 lr_st Hlt_a_false.
    list_store_solver R2 lr_st Hlt_a_false.
    list_store_solver R3 lr_st Hlt_a_false.
    list_store_solver R4 lr_st Hlt_a_false.
    list_store_solver R5 lr_st Hlt_a_false.
    list_store_solver R6 lr_st Hlt_a_false.
    list_store_solver R7 lr_st Hlt_a_false.
    rewrite ! app_nil_l in *.
    rewrite <- Hjit.
    rewrite <- Htl.
    apply my_app_tail.
    unfold jit_alu32_thumb_upd_store.
    rewrite Heq_a_true; auto.
  }

  destruct (breg_eq R9 a) as [Hr9_eq | Hr9_neq].
  { subst a.
    rewrite jit_alu32_thumb_upd_store_reset_same in Htl.
    do 10 (rewrite jit_alu32_thumb_upd_store_reset_other in Htl; [| intro HF; inversion HF]).
    list_store_solver R0 lr_st Hlt_a_false.
    list_store_solver R1 lr_st Hlt_a_false.
    list_store_solver R2 lr_st Hlt_a_false.
    list_store_solver R3 lr_st Hlt_a_false.
    list_store_solver R4 lr_st Hlt_a_false.
    list_store_solver R5 lr_st Hlt_a_false.
    list_store_solver R6 lr_st Hlt_a_false.
    list_store_solver R7 lr_st Hlt_a_false.
    list_store_solver R8 lr_st Hlt_a_false.
    rewrite ! app_nil_l in *.
    rewrite <- Hjit.
    rewrite <- Htl.
    apply my_app_tail.
    unfold jit_alu32_thumb_upd_store.
    rewrite Heq_a_true; auto.
  }

  destruct (breg_eq R10 a) as [Hr10_eq | Hr10_neq].
  { subst a.
    rewrite jit_alu32_thumb_upd_store_reset_same in Htl.
    do 10 (rewrite jit_alu32_thumb_upd_store_reset_other in Htl; [| intro HF; inversion HF]).
    list_store_solver R0 lr_st Hlt_a_false.
    list_store_solver R1 lr_st Hlt_a_false.
    list_store_solver R2 lr_st Hlt_a_false.
    list_store_solver R3 lr_st Hlt_a_false.
    list_store_solver R4 lr_st Hlt_a_false.
    list_store_solver R5 lr_st Hlt_a_false.
    list_store_solver R6 lr_st Hlt_a_false.
    list_store_solver R7 lr_st Hlt_a_false.
    list_store_solver R8 lr_st Hlt_a_false.
    list_store_solver R9 lr_st Hlt_a_false.
    rewrite ! app_nil_l in *.
    rewrite <- Hjit.
    rewrite <- Htl.
    rewrite ! app_nil_r in *.
    unfold jit_alu32_thumb_upd_store.
    rewrite Heq_a_true; auto.
  }

  exfalso.
  destruct a;
  match goal with
  | H: ?X <> ?X |- _ =>
    apply H; reflexivity
  end.
Qed.

Lemma jit_alu32_thumb_store_refine_eq:
  forall st_set lr_st bl
  (HNoDup: NoDup st_set)
  (HSort: sort st_set)
  (Hst: eq_set_map st_set lr_st)
  (Hjit: jit_alu32_thumb_store st_set = bl),
      jit_alu32_thumb_store_refine lr_st = bl.
Proof.
  induction st_set; simpl; intros.
  {
    unfold eq_set_map in Hst.
    subst bl.
    unfold jit_alu32_thumb_store_refine.
    assert (Heq: forall r : breg, eval_listset_regmap r lr_st = false).
    - intros.
      specialize (Hst r).
      symmetry in Hst.
      apply neg_false in Hst.
      apply Bool.not_true_is_false.
      auto.
    - unfold jit_alu32_thumb_upd_store.
      repeat match goal with
      | |- context[if eval_listset_regmap ?X _ then _ else _] =>
        specialize (Heq X) as Hr0; rewrite Hr0; clear Hr0; try rewrite app_nil_l
      end.
      reflexivity.
  }

  assert (Heq_a_true: eval_listset_regmap a lr_st = true). {
    clear - Hst.
    unfold eq_set_map in Hst.
    apply Hst.
    left; auto.
  }

  assert (Hlt_a_false: forall r, Z.leb (z_of_breg a) (z_of_breg r) = false ->
    eval_listset_regmap r lr_st = false). {
    intros r Hle.
    eapply Z.leb_gt in Hle.
    clear - HNoDup HSort Hst Hle.
    unfold eq_set_map in Hst.
    specialize (Hst r).
    apply not_iff_compat in Hst.
    apply Bool.not_true_is_false.
    apply Hst.
    intro HF.
    destruct HF as [HF | HF].
    { subst a. apply Z.lt_irrefl in Hle. auto. }

    eapply isSort_aux_not_in in Hle; eauto.
  }

  eapply jit_alu32_thumb_store_refine_reset; eauto.
  rewrite <- Hjit.
  simpl.
  f_equal.
  eapply IHst_set; eauto.
  - rewrite NoDup_cons_iff in HNoDup.
    destruct HNoDup as (_ & Heq); auto.
  - clear - HSort.
    unfold sort in *.
    inversion HSort.
    subst.
    auto.
  - clear - HNoDup Hst.
    unfold eq_set_map in *.
    intros.
    specialize (Hst r).
    destruct (breg_eq r a) as [Heq | Hneq].
    + subst r.
      split; intro HF.
      * rewrite NoDup_cons_iff in HNoDup.
        destruct HNoDup as (Hneq & Heq); auto.
      * rewrite eval_listset_regmap_reset_listset_regmap_same in HF.
        inversion HF.
    + split; intro HF.
      * rewrite eval_listset_regmap_reset_listset_regmap_other; auto.
        apply Hst.
        right; auto.
      * rewrite eval_listset_regmap_reset_listset_regmap_other in HF; auto.
        apply Hst in HF.
        destruct HF as [Heq | HF]; [exfalso; apply Hneq; auto | auto].
Qed.

Lemma jit_alu32_thumb_upd_reset_reset_same:
  forall r lr_st,
  jit_alu32_thumb_upd_reset r (reset_listset_regmap r lr_st) = [].
Proof.
  intros.
  unfold jit_alu32_thumb_upd_reset.
  rewrite eval_listset_regmap_reset_listset_regmap_same.
  reflexivity.
Qed.

Lemma jit_alu32_thumb_upd_reset_reset_other:
  forall r r' lr_st,
  r <> r' ->
  jit_alu32_thumb_upd_reset r (reset_listset_regmap r' lr_st) = jit_alu32_thumb_upd_reset r lr_st.
Proof.
  intros.
  unfold jit_alu32_thumb_upd_reset.
  rewrite eval_listset_regmap_reset_listset_regmap_other; auto.
Qed.

Ltac list_reset_solver X lr_st H :=
  match goal with
  | |- _ =>
    assert (Heq: jit_alu32_thumb_upd_reset X lr_st = []) by
    (unfold jit_alu32_thumb_upd_reset; rewrite H; auto);
    rewrite Heq in *; clear Heq
  end.

Lemma jit_alu32_thumb_reset_refine1_reset:
  forall a lr_st tl bl
  (Hlt_a_false : forall r : breg,
              (z_of_breg a <=? z_of_breg r) = false -> eval_listset_regmap r lr_st = false)
  (Htl: jit_alu32_thumb_reset1_refine (reset_listset_regmap a lr_st) = tl)
  (Hjit : (if Int.ltu (Int.repr 3) (int_of_breg a) && Int.ltu (int_of_breg a) (Int.repr 11)
        then
         [jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg a) (int_of_ireg IR13)
            (Int.mul (int_of_breg a) (Int.repr 4))]
        else []) ++ tl = bl)
  (Heq_a_true : eval_listset_regmap a lr_st = true),
    jit_alu32_thumb_reset1_refine lr_st = bl.
Proof.

  unfold jit_alu32_thumb_reset1_refine; intros.
  destruct (breg_eq R0 a) as [Hr0_eq | Hr0_neq].
  { subst a.
    change (Int.ltu (Int.repr 3) (int_of_breg R0) && Int.ltu (int_of_breg R0) (Int.repr 11)) with false in Hjit.
    simpl in Hjit.
    subst tl. auto.
  }
  destruct (breg_eq R1 a) as [Hr1_eq | Hr1_neq].
  { subst a.
    change (Int.ltu (Int.repr 3) (int_of_breg R1) && Int.ltu (int_of_breg R1) (Int.repr 11)) with false in Hjit.
    simpl in Hjit.
    subst tl. auto.
  }

  destruct (breg_eq R2 a) as [Hr2_eq | Hr2_neq].
  { subst a.
    change (Int.ltu (Int.repr 3) (int_of_breg R2) && Int.ltu (int_of_breg R2) (Int.repr 11)) with false in Hjit.
    simpl in Hjit.
    subst tl. auto.
  }

  destruct (breg_eq R3 a) as [Hr3_eq | Hr3_neq].
  { subst a.
    change (Int.ltu (Int.repr 3) (int_of_breg R3) && Int.ltu (int_of_breg R3) (Int.repr 11)) with false in Hjit.
    simpl in Hjit.
    subst tl. auto.
  }

  destruct (breg_eq R4 a) as [Hr4_eq | Hr4_neq].
  { subst a.
    change (Int.ltu (Int.repr 3) (int_of_breg R4) && Int.ltu (int_of_breg R4) (Int.repr 11)) with true in Hjit.
    simpl in Hjit.
    rewrite jit_alu32_thumb_upd_reset_reset_same in Htl.
    do 6 (rewrite jit_alu32_thumb_upd_reset_reset_other in Htl; [| intro HF; inversion HF]).
    rewrite ! app_nil_l in *.
    rewrite <- Hjit.
    rewrite <- Htl.
    rewrite my_app_hd.
    apply my_app_tail.
    unfold jit_alu32_thumb_upd_reset.
    rewrite Heq_a_true; auto.
  }

  destruct (breg_eq R5 a) as [Hr5_eq | Hr5_neq].
  { subst a.
    change (Int.ltu (Int.repr 3) (int_of_breg R5) && Int.ltu (int_of_breg R5) (Int.repr 11)) with true in Hjit.
    simpl in Hjit.
    rewrite jit_alu32_thumb_upd_reset_reset_same in Htl.
    do 6 (rewrite jit_alu32_thumb_upd_reset_reset_other in Htl; [| intro HF; inversion HF]).
    list_reset_solver R4 lr_st Hlt_a_false.
    rewrite ! app_nil_l in *.
    rewrite <- Hjit.
    rewrite <- Htl.
    rewrite my_app_hd.
    apply my_app_tail.
    unfold jit_alu32_thumb_upd_reset.
    rewrite Heq_a_true; auto.
  }

  destruct (breg_eq R6 a) as [Hr6_eq | Hr6_neq].
  { subst a.
    change (Int.ltu (Int.repr 3) (int_of_breg R6) && Int.ltu (int_of_breg R6) (Int.repr 11)) with true in Hjit.
    simpl in Hjit.
    rewrite jit_alu32_thumb_upd_reset_reset_same in Htl.
    do 6 (rewrite jit_alu32_thumb_upd_reset_reset_other in Htl; [| intro HF; inversion HF]).
    list_reset_solver R4 lr_st Hlt_a_false.
    list_reset_solver R5 lr_st Hlt_a_false.
    rewrite ! app_nil_l in *.
    rewrite <- Hjit.
    rewrite <- Htl.
    rewrite my_app_hd.
    apply my_app_tail.
    unfold jit_alu32_thumb_upd_reset.
    rewrite Heq_a_true; auto.
  }

  destruct (breg_eq R7 a) as [Hr7_eq | Hr7_neq].
  { subst a.
    change (Int.ltu (Int.repr 3) (int_of_breg R7) && Int.ltu (int_of_breg R7) (Int.repr 11)) with true in Hjit.
    simpl in Hjit.
    rewrite jit_alu32_thumb_upd_reset_reset_same in Htl.
    do 6 (rewrite jit_alu32_thumb_upd_reset_reset_other in Htl; [| intro HF; inversion HF]).
    list_reset_solver R4 lr_st Hlt_a_false.
    list_reset_solver R5 lr_st Hlt_a_false.
    list_reset_solver R6 lr_st Hlt_a_false.
    rewrite ! app_nil_l in *.
    rewrite <- Hjit.
    rewrite <- Htl.
    rewrite my_app_hd.
    apply my_app_tail.
    unfold jit_alu32_thumb_upd_reset.
    rewrite Heq_a_true; auto.
  }

  destruct (breg_eq R8 a) as [Hr8_eq | Hr8_neq].
  { subst a.
    change (Int.ltu (Int.repr 3) (int_of_breg R8) && Int.ltu (int_of_breg R8) (Int.repr 11)) with true in Hjit.
    simpl in Hjit.
    rewrite jit_alu32_thumb_upd_reset_reset_same in Htl.
    do 6 (rewrite jit_alu32_thumb_upd_reset_reset_other in Htl; [| intro HF; inversion HF]).
    list_reset_solver R4 lr_st Hlt_a_false.
    list_reset_solver R5 lr_st Hlt_a_false.
    list_reset_solver R6 lr_st Hlt_a_false.
    list_reset_solver R7 lr_st Hlt_a_false.
    rewrite ! app_nil_l in *.
    rewrite <- Hjit.
    rewrite <- Htl.
    rewrite my_app_hd.
    apply my_app_tail.
    unfold jit_alu32_thumb_upd_reset.
    rewrite Heq_a_true; auto.
  }

  destruct (breg_eq R9 a) as [Hr9_eq | Hr9_neq].
  { subst a.
    change (Int.ltu (Int.repr 3) (int_of_breg R9) && Int.ltu (int_of_breg R9) (Int.repr 11)) with true in Hjit.
    simpl in Hjit.
    rewrite jit_alu32_thumb_upd_reset_reset_same in Htl.
    do 6 (rewrite jit_alu32_thumb_upd_reset_reset_other in Htl; [| intro HF; inversion HF]).
    list_reset_solver R4 lr_st Hlt_a_false.
    list_reset_solver R5 lr_st Hlt_a_false.
    list_reset_solver R6 lr_st Hlt_a_false.
    list_reset_solver R7 lr_st Hlt_a_false.
    list_reset_solver R8 lr_st Hlt_a_false.
    rewrite ! app_nil_l in *.
    rewrite <- Hjit.
    rewrite <- Htl.
    rewrite my_app_hd.
    apply my_app_tail.
    unfold jit_alu32_thumb_upd_reset.
    rewrite Heq_a_true; auto.
  }

  destruct (breg_eq R10 a) as [Hr10_eq | Hr10_neq].
  { subst a.
    change (Int.ltu (Int.repr 3) (int_of_breg R10) && Int.ltu (int_of_breg R10) (Int.repr 11)) with true in Hjit.
    simpl in Hjit.
    rewrite jit_alu32_thumb_upd_reset_reset_same in Htl.
    do 6 (rewrite jit_alu32_thumb_upd_reset_reset_other in Htl; [| intro HF; inversion HF]).
    list_reset_solver R4 lr_st Hlt_a_false.
    list_reset_solver R5 lr_st Hlt_a_false.
    list_reset_solver R6 lr_st Hlt_a_false.
    list_reset_solver R7 lr_st Hlt_a_false.
    list_reset_solver R8 lr_st Hlt_a_false.
    list_reset_solver R9 lr_st Hlt_a_false.
    rewrite ! app_nil_l in *.
    rewrite <- Hjit.
    rewrite <- Htl.
    unfold jit_alu32_thumb_upd_reset.
    rewrite Heq_a_true; auto.
  }

  exfalso.
  destruct a;
  match goal with
  | H: ?X <> ?X |- _ =>
    apply H; reflexivity
  end.
Qed.

Lemma jit_alu32_thumb_reset1_refine_eq:
  forall ld_set lr_st bl
  (HNoDup: NoDup ld_set)
  (HSort: sort ld_set)
  (Hst: eq_set_map ld_set lr_st)
  (Hjit: jit_alu32_thumb_reset1 ld_set = bl),
      jit_alu32_thumb_reset1_refine lr_st = bl.
Proof.
  induction ld_set; simpl; intros.
  {
    unfold eq_set_map in Hst.
    subst bl.
    unfold jit_alu32_thumb_reset1_refine.
    assert (Heq: forall r : breg, eval_listset_regmap r lr_st = false).
    - intros.
      specialize (Hst r).
      symmetry in Hst.
      apply neg_false in Hst.
      apply Bool.not_true_is_false.
      auto.
    - unfold jit_alu32_thumb_upd_reset.
      repeat match goal with
      | |- context[if eval_listset_regmap ?X _ then _ else _] =>
        specialize (Heq X) as Hr0; rewrite Hr0; clear Hr0; try rewrite app_nil_l
      end.
      reflexivity.
  }

  assert (Heq_a_true: eval_listset_regmap a lr_st = true). {
    clear - Hst.
    unfold eq_set_map in Hst.
    apply Hst.
    left; auto.
  }

  assert (Hlt_a_false: forall r, Z.leb (z_of_breg a) (z_of_breg r) = false ->
    eval_listset_regmap r lr_st = false). {
    intros r Hle.
    eapply Z.leb_gt in Hle.
    clear - HNoDup HSort Hst Hle.
    unfold eq_set_map in Hst.
    specialize (Hst r).
    apply not_iff_compat in Hst.
    apply Bool.not_true_is_false.
    apply Hst.
    intro HF.
    destruct HF as [HF | HF].
    { subst a. apply Z.lt_irrefl in Hle. auto. }

    eapply isSort_aux_not_in in Hle; eauto.
  }

  eapply jit_alu32_thumb_reset_refine1_reset; eauto.
  rewrite <- Hjit.
  f_equal.
  eapply IHld_set; eauto.
  - rewrite NoDup_cons_iff in HNoDup.
    destruct HNoDup as (_ & Heq); auto.
  - clear - HSort.
    unfold sort in *.
    inversion HSort.
    subst.
    auto.
  - clear - HNoDup Hst.
    unfold eq_set_map in *.
    intros.
    specialize (Hst r).
    destruct (breg_eq r a) as [Heq | Hneq].
    + subst r.
      split; intro HF.
      * rewrite NoDup_cons_iff in HNoDup.
        destruct HNoDup as (Hneq & Heq); auto.
      * rewrite eval_listset_regmap_reset_listset_regmap_same in HF.
        inversion HF.
    + split; intro HF.
      * rewrite eval_listset_regmap_reset_listset_regmap_other; auto.
        apply Hst.
        right; auto.
      * rewrite eval_listset_regmap_reset_listset_regmap_other in HF; auto.
        apply Hst in HF.
        destruct HF as [Heq | HF]; [exfalso; apply Hneq; auto | auto].
Qed.

Lemma jit_alu32_thumb_reset_refine_eq:
  forall ld_set lr_st bl
  (HNoDup: NoDup ld_set)
  (HSort: sort ld_set)
  (Hst: eq_set_map ld_set lr_st)
  (Hjit: jit_alu32_thumb_reset ld_set = bl),
      jit_alu32_thumb_reset_refine lr_st = bl.
Proof.
  unfold jit_alu32_thumb_reset, jit_alu32_thumb_reset_refine; intros.
  rewrite <- Hjit.
  f_equal.
  erewrite jit_alu32_thumb_reset1_refine_eq; eauto.
Qed.


Lemma jit_alu32_aux_refine_eq:
  forall l bl,
    jit_alu32_aux l = Some bl ->
    jit_alu32_aux_refine l = Some bl.
Proof.
  unfold jit_alu32_aux, jit_alu32_aux_refine; intros.
  assert (Heq1: eq_set_map [] init_listset_regmap). {
    unfold eq_set_map, init_listset_regmap.
    intros.
    split; intro HF.
    - inversion HF.
    - destruct r; simpl in HF; inversion HF.
  }
  destruct jit_sequence as [((cl & ld_set) & st_set)|] eqn: Hseq.
  { eapply jit_sequence_refine_eq in Hseq; eauto; try (apply NoDup_nil).
    destruct Hseq as (ldr1 & lr2 & Hseq_r & Heq_r1 & Heq_r2 & Hno1 & Hno2).
    rewrite Hseq_r.
    destruct cl; auto.
    destruct jit_alu32_thumb_pc as [l_pc | ]; auto.
    apply eq_set_map_sort_list_same in Heq_r1.
    apply eq_set_map_sort_list_same in Heq_r2.
    injection H as Heq.
    rewrite <- Heq.
    simpl.
    repeat f_equal.
    - erewrite jit_alu32_thumb_store_refine_eq with (st_set := sort_listset st_set); eauto.
      + apply NoDup_sort_listset; auto.
      + apply sort_sort_listset.
    - erewrite jit_alu32_thumb_reset_refine_eq with (ld_set := sort_listset ld_set); eauto.
      + apply NoDup_sort_listset; auto.
      + apply sort_sort_listset.
  }
  inversion H.
Qed.


Lemma jit_alu32_refine_eq:
  forall l bl,
    jit_alu32 l = Some bl ->
    jit_alu32_refine l = Some bl.
Proof.
  unfold jit_alu32, jit_alu32_refine; intros.
  destruct jit_alu32_aux as [tl | ] eqn: Heq; [| inversion H].
  erewrite jit_alu32_aux_refine_eq; eauto.
Qed.