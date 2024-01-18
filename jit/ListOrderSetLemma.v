From bpf.rbpf32 Require Import TSSyntax.
From Coq Require Import ZArith Bool Lia List SetoidList.

Open Scope nat_scope.
Import ListNotations.

Lemma set_add_same:
  forall (l: list breg) (x: breg),
    (set_add x (set_add x l)) = set_add x l.
Proof.
  induction l; intros.
  - simpl.
    unfold breg_compare.
    rewrite Z.compare_refl.
    auto.
  - simpl.
    unfold breg_compare.
    destruct (_ ?= _)%Z eqn: Hcmp.
    + simpl; unfold breg_compare; rewrite Hcmp.
      auto.
    + simpl; unfold breg_compare; rewrite Hcmp.
      rewrite Z.compare_refl; auto.
    + simpl; unfold breg_compare; rewrite Hcmp.
      f_equal.
      apply IHl.
Qed.

Lemma set_mem_in_true_iff:
  forall r l,
  set_ok l ->
  set_mem r l = true <-> List.In r l.
Proof.
  unfold set_mem.
  split; intros.
  - rewrite BregOrderListSet.mem_spec in H0; auto.
    apply InA_alt in H0.
    destruct H0 as (y & Heq & Hin).
    subst; auto.
  - apply BregOrderListSet.ML.ListIn_In in H0.
    rewrite BregOrderListSet.mem_spec; auto.
Qed.

Lemma set_mem_in_false_iff:
  forall r l,
  set_ok l ->
  set_mem r l = false <-> ~ List.In r l.
Proof.
  split; intros.
  - intro HF.
    rewrite <- set_mem_in_true_iff in HF; auto.
    rewrite HF in H0.
    inversion H0.
  - rewrite <- set_mem_in_true_iff in H0; auto.
    apply not_true_is_false; auto.
Qed.

Lemma set_add_intro1: forall l a b, In a (set_add b l) -> a = b \/ In a l.
Proof.
  induction l; simpl; intros.
  - destruct H; inversion H.
    left; auto.
  - unfold breg_compare in H.
    destruct (_ ?= _)%Z eqn: Hcmp.
    + simpl in H.
      destruct H; auto.
    + simpl in H.
      destruct H; auto.
    + simpl in H.
      destruct H; auto.
      specialize (IHl _ _ H).
      destruct IHl; auto.
Qed.

Lemma set_add_in_1: forall l a, In a (set_add a l).
Proof.
  induction l; simpl; intros.
  - left; auto.
  - unfold breg_compare.
    destruct (_ ?= _)%Z eqn: Hcmp.
    + rewrite Z.compare_eq_iff in Hcmp.
      rewrite z_of_breg_eq_iff in Hcmp; subst.
      simpl.
      left; auto.
    + rewrite Z.compare_lt_iff in Hcmp.
      apply Z.lt_neq in Hcmp.
      simpl.
      left; auto.
    + rewrite Z.compare_gt_iff in Hcmp.
      apply Z.lt_neq in Hcmp.
      simpl.
      right.
      apply IHl; auto.
Qed.

Lemma set_add_in_2: forall l a b, In a l -> In a (set_add b l).
Proof.
  induction l; simpl; intros.
  - auto.
  - unfold breg_compare.
    destruct (_ ?= _)%Z eqn: Hcmp.
    + simpl.
      auto.
    + simpl.
      right; auto.
    + simpl.
      destruct H; auto.
Qed.

Lemma set_add_intro2: forall l a b, a = b \/ In a l -> In a (set_add b l).
Proof.
  intros.
  destruct H.
  - subst.
    apply set_add_in_1.
  - apply set_add_in_2; auto.
Qed.

Lemma set_add_iff l a b : In a (set_add b l) <-> a = b \/ In a l.
Proof.
  split.
  - apply set_add_intro1.
  - apply set_add_intro2.
Qed.

Lemma set_mem_add_same:
  forall l r,
  set_mem r (set_add r l) = true.
Proof.
  induction l; simpl; intros.
  - unfold breg_compare.
    rewrite Z.compare_refl.
    auto.
  - unfold breg_compare.
    destruct (_ ?= _)%Z eqn: Hcmp.
    + rewrite Z.compare_eq_iff in Hcmp.
      rewrite z_of_breg_eq_iff in Hcmp; subst.
      simpl.
      unfold breg_compare.
      rewrite Z.compare_refl; auto.
    + simpl.
      unfold breg_compare.
      rewrite Z.compare_refl; auto.
    + simpl.
      unfold breg_compare.
      rewrite Hcmp.
      apply IHl; auto.
Qed.

Lemma InA_ListIn_iff:
  forall {A: Type} l (x: A), InA eq x l <-> In x l.
Proof.
  intros.
  apply iff_trans with (B := (exists y, eq x y /\ In y l)).
  - apply InA_alt.
  - split; intro HF.
    + destruct HF as (y & Heq & HF).
      subst.
      auto.
    + exists x.
      split; auto.
Qed.

Lemma set_union_intro1 :
 forall x y a, set_ok x -> set_ok y -> List.In a x -> List.In a (set_union x y).
Proof.
  intros.
  rewrite <- InA_ListIn_iff.
  rewrite BregOrderListSet.union_spec; auto.
Qed.

Lemma set_add_ok:
  forall l r, set_ok l -> set_ok (set_add r l).
Proof.
  intros. eapply BregOrderListSet.add_ok; eauto.
Qed.

Lemma NoDupA_no_in:
  forall {A: Type} l (a: A), NoDupA eq (a :: l) -> ~ (List.In a l).
Proof.
  induction l; simpl; intros.
  { auto. }

  apply Classical_Prop.and_not_or.
  split.
  - inversion H; subst.
    intros HF.
    subst.
    inversion H; subst.
    apply H4.
    eapply InA_ListIn_iff.
    left; auto.
  - apply IHl.
    inversion H; subst.
    constructor.
    + intro HF.
      apply H2.
      apply InA_ListIn_iff.
      apply InA_ListIn_iff in HF.
      right; auto.
    + inversion H3; subst.
      auto.
Qed.

Lemma set_add_nodup:
  forall l a, set_ok l -> NoDupA eq l -> NoDupA eq (set_add a l).
Proof.
  induction l; simpl; intros.
  - constructor.
    + intro HF.
      inversion HF.
    + constructor. ../..
Qed.