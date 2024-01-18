From compcert.lib Require Import Integers Maps.
From compcert.arm Require Import ABinSem.

From Coq Require Import ZArith Lia.
Open Scope bool_scope.
Open Scope Z_scope.

Lemma ab_setN_other:
  forall vl c p q,
  (forall r, p <= r < p + Z.of_nat (length vl) -> r <> q) ->
  ZMap.get q (setN vl p c) = ZMap.get q c.
Proof.
  induction vl; intros; simpl.
  auto.
  simpl length in H. rewrite Nat2Z.inj_succ in H.
  transitivity (ZMap.get q (ZMap.set p a c)).
  apply IHvl. intros. apply H. lia.
  apply ZMap.gso. apply not_eq_sym. apply H. lia.
Qed.

Lemma ab_setN_outside:
  forall vl c p q,
  q < p \/ q >= p + Z.of_nat (length vl) ->
  ZMap.get q (setN vl p c) = ZMap.get q c.
Proof.
  intros. apply ab_setN_other.
  intros. lia.
Qed.

Remark ab_getN_setN_same:
  forall vl p c,
  getN (length vl) p (setN vl p c) = vl.
Proof.
  induction vl; intros; simpl.
  auto.
  f_equal.
  rewrite ab_setN_outside. apply ZMap.gss. lia.
  apply IHvl.
Qed.

Lemma ab_getN_exten:
  forall c1 c2 n p,
  (forall i, p <= i < p + Z.of_nat n -> ZMap.get i c1 = ZMap.get i c2) ->
  getN n p c1 = getN n p c2.
Proof.
  induction n; intros. auto. rewrite Nat2Z.inj_succ in H. simpl. f_equal.
  apply H. lia. apply IHn. intros. apply H. lia.
Qed.

Lemma ab_getN_setN_disjoint:
  forall vl q c n p,
  Intv.disjoint (p, p + Z.of_nat n) (q, q + Z.of_nat (length vl)) ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. apply ab_getN_exten. intros. apply ab_setN_other.
  intros; red; intros; subst r. eelim H; eauto.
Qed.

Remark ab_getN_setN_outside:
  forall vl q c n p,
  p + Z.of_nat n <= q \/ q + Z.of_nat (length vl) <= p ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. apply ab_getN_setN_disjoint. apply Intv.disjoint_range. auto.
Qed.