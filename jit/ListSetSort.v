From bpf.rbpf32 Require Import TSSyntax.

From Coq Require Import List ZArith Arith ListSet Lia Sorted.
Import ListNotations.
Open Scope Z_scope.

Fixpoint insert (l: listset) (a: breg) : listset :=
  match l with
  | [] => [a]
  | hd :: tl => (*
    if Z.leb (z_of_breg a) (z_of_breg hd) then
      a :: l *)
    if Z.ltb (z_of_breg a) (z_of_breg hd) then
      a :: l
    else if Z.eqb (z_of_breg a) (z_of_breg hd) then
      l
    else
      hd :: (insert tl a)
  end.

Fixpoint sort_listset (l: listset) : listset :=
  match l with
  | [] => []
  | hd :: tl => insert (sort_listset tl) hd
  end.

Lemma In_insert_intro1:
  forall l a b, In a (insert l b) -> a = b \/ In a l.
Proof.
  induction l; simpl; intros.
  { destruct H; auto. }

  destruct (_ <? _)%Z eqn: Hcmp.
  { destruct H.
    - subst.
      left; auto.
    - destruct H.
      + subst.
        auto.
      + auto.
  }

  destruct (_ =? _)%Z eqn: Heq.
  { rewrite Z.eqb_eq in Heq.
    apply z_of_breg_eq_iff in Heq.
    subst a.
    destruct H.
    - subst b; auto.
    - auto.
  }

  destruct H.
  { subst.
    auto. }

  specialize (IHl _ _ H).
  destruct IHl; auto.
Qed.

Lemma In_insert_same:
  forall l a, In a (insert l a).
Proof.
  induction l; simpl; intros.
  { auto. }

  destruct (_ <? _)%Z eqn: Hcmp.
  { left; auto. }

  destruct (_ =? _)%Z eqn: Heq.
  { rewrite Z.eqb_eq in Heq.
    apply z_of_breg_eq_iff in Heq.
    subst a.
    left; auto.
  }
  right.
  apply IHl.
Qed.

Lemma In_insert_intro2_aux1:
  forall l a b, a = b -> In a (insert l b).
Proof.
  intros.
  subst.
  apply In_insert_same.
Qed.

Lemma In_insert_intro2_aux2:
  forall l a b, In a l -> In a (insert l b).
Proof.
  induction l; simpl; intros.
  { destruct H; auto. }

  destruct (_ <? _)%Z eqn: Hcmp.
  { destruct H.
    - subst.
      right; left; auto.
    - right; right; auto.
  }

  destruct (_ =? _)%Z eqn: Heq.
  { rewrite Z.eqb_eq in Heq.
    apply z_of_breg_eq_iff in Heq.
    subst a.
    destruct H.
    - subst b.
      left; auto.
    - right; auto.
  }

  destruct H.
  - subst.
    left; auto.
  - right.
    apply IHl; auto.
Qed.

Lemma In_insert_intro2:
  forall l a b, a = b \/ In a l -> In a (insert l b).
Proof.
  intros.
  destruct H.
  - apply In_insert_intro2_aux1; auto.
  - apply In_insert_intro2_aux2; auto.
Qed.

Lemma NoDup_insert:
  forall l a, NoDup (a :: l) -> NoDup (insert l a).
Proof.
  induction l; simpl; intros.
  { auto. }

  destruct (_ <? _)%Z eqn: Hcmp.
  { auto. }

  destruct (_ =? _)%Z eqn: Heq.
  { rewrite Z.eqb_eq in Heq.
    apply z_of_breg_eq_iff in Heq.
    subst a.
    rewrite NoDup_cons_iff in H.
    destruct H; auto.
  }

  inversion H; subst.
  inversion H3; subst.

  constructor.
  - intros HF.
    apply H4.
    eapply In_insert_intro1 in HF; eauto.
    destruct HF as [HF | HF]; [| auto].
    subst.
    exfalso.
    inversion H; subst.
    apply H6.
    left; auto.
  - apply IHl; auto.
    constructor; auto.
    intro HF.
    apply H2.
    right; auto.
Qed.

Lemma In_sort_listset_intro1:
  forall l a, In a (sort_listset l) -> In a l.
Proof.
  induction l; simpl; intros.
  { auto. }

  apply In_insert_intro1 in H.
  destruct H.
  - subst; left; auto.
  - right.
    apply IHl; auto.
Qed.

Lemma In_sort_listset_intro2:
  forall l a, In a l -> In a (sort_listset l).
Proof.
  induction l; simpl; intros.
  { auto. }

  apply In_insert_intro2.
  destruct H.
  - subst; left; auto.
  - right.
    apply IHl; auto.
Qed.

Lemma NoDup_sort_listset:
  forall l,
    NoDup l -> NoDup (sort_listset l).
Proof.
  induction l; simpl; intros.
  { auto. }

  eapply NoDup_insert; eauto.
  inversion H; subst.
  constructor.
  - intro HF.
    apply H2.
    apply In_sort_listset_intro1; auto.
  - apply IHl; auto.
Qed.


Definition hdrel := HdRel (fun x y => (z_of_breg x < z_of_breg y)%Z).


Lemma hdrel_insert:
  forall l a a0, hdrel a l -> (z_of_breg a0 > z_of_breg a)%Z -> hdrel a (insert l a0).
Proof.
  unfold hdrel.
  induction l; simpl; intros.
  { constructor. lia. }

  inversion H; subst.
  destruct (_ <? _)%Z eqn: Hcmp.
  { rewrite <- Zlt_is_lt_bool in Hcmp.
    repeat constructor; auto.
    lia.
  }

  destruct (_ =? _)%Z eqn: Heq.
  {
    rewrite Z.eqb_eq in Heq.
    rewrite z_of_breg_eq_iff in Heq.
    subst a.
    auto.
  }
  constructor.
  lia.
Qed.

Definition sort := Sorted (fun x y => (z_of_breg x < z_of_breg y)%Z).

Lemma sort_insert:
  forall l a, sort l -> sort (insert l a).
Proof.
  induction l; simpl; intros.
  { unfold sort.
    constructor; constructor.
  }

  inversion H; subst.
  destruct (_ <? _)%Z eqn: Hcmp.
  { rewrite <- Zlt_is_lt_bool in Hcmp.
    repeat constructor; auto.
  }

  destruct (_ =? _)%Z eqn: Heq.
  {
    rewrite Z.eqb_eq in Heq.
    rewrite z_of_breg_eq_iff in Heq.
    subst a.
    auto.
  }

  constructor.
  - apply IHl; auto.
  - apply hdrel_insert; auto.
    lia.
Qed.

Lemma sort_sort_listset:
  forall l, sort (sort_listset l).
Proof.
  induction l; simpl; intros.
  { constructor. }

  apply sort_insert; auto.
Qed.


Lemma isSort_aux_not_in: 
  forall l a r,
  sort (a :: l) ->
  z_of_breg r < z_of_breg a ->
    ~ (In r l).
Proof.
  induction l; simpl; intros.
  { auto. }

  intro HF.
  destruct HF as [HF | HF].
  { subst a.
    inversion H.
    subst.
    inversion H4.
    subst.
    lia.
  }

  inversion H.
  subst.
  specialize (IHl a r H3).
  apply IHl; eauto.
  inversion H4.
  subst.
  lia.
Qed.

(*

Fixpoint IsSort_aux (a: breg) (l: listset): Prop :=
  match l with
  | [] => True
  | hd :: tl =>
    if Z.ltb (z_of_breg a) (z_of_breg hd) then
      IsSort_aux hd tl
    else
      False
  end.

Definition IsSort (l: listset) : Prop :=
  match l with
  | [] => True
  | hd :: tl => IsSort_aux hd tl
  end.

Fixpoint IsSort2 (l: listset) : Prop :=
  match l with
  | [] => True
  | hd1 :: tl =>
    match tl with
    | [] => True
    | hd2 :: tl1 =>
      if Z.ltb (z_of_breg hd1) (z_of_breg hd2) then
        IsSort2 tl
      else
        False
    end
  end.

Lemma IsSort_same_IsSort2:
  forall l, IsSort l <-> IsSort2 l.
Proof.
  induction l; simpl; intros.
  { split; auto. }

  destruct l.
  { split; auto. }

  destruct (_ <? _) eqn: Hle.
  { rewrite <- IHl.
    simpl.
    rewrite Hle.
    split; auto.
  }

  simpl.
  rewrite Hle.
  split; auto.
Qed.*)