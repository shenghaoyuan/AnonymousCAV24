From compcert.lib Require Import Integers Coqlib.

From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

Lemma zle_true_iff:
  forall (x y : Z), x <= y <-> @eq bool (@proj_sumbool (Z.le x y) (Z.gt x y) (zle x y)) true.
Proof.
  intros.
  split; intro.
  - apply zle_true; auto.
  - destruct zle.
    + assumption.
    + inversion H.
Qed.

Lemma zle_false_iff:
  forall (x y : Z), x > y <-> @eq bool (@proj_sumbool (Z.le x y) (Z.gt x y) (zle x y)) false.
Proof.
  intros.
  split; intro.
  - apply zle_false; auto.
  - destruct zle.
    + inversion H.
    + assumption.
Qed.

Lemma zlt_true_iff:
  forall (x y : Z), x < y <-> @eq bool (@proj_sumbool (Z.lt x y) (Z.ge x y) (zlt x y)) true.
Proof.
  intros.
  split; intro.
  - apply zlt_true; auto.
  - destruct zlt.
    + assumption.
    + inversion H.
Qed.

Lemma zlt_false_iff:
  forall (x y : Z), x >= y <-> @eq bool (@proj_sumbool (Z.lt x y) (Z.ge x y) (zlt x y)) false.
Proof.
  intros.
  split; intro.
  - apply zlt_false; auto.
  - destruct zlt.
    + inversion H.
    + assumption.
Qed.

Lemma same_bits_eq_iff:
  forall x y,
  (forall i, 0 <= i < Int.zwordsize -> Int.testbit x i = Int.testbit y i) <-> x = y.
Proof.
  intros.
  split; intros.
  - apply Int.same_bits_eq; auto.
  - subst x. auto.
Qed.

(*
Lemma unsigned_bitfield_extract_high_zero:
  forall i pos width
    (Hrange: 0 < pos /\ 0 < width /\ pos+width = Int.zwordsize)
    (Hhi: Int.unsigned_bitfield_extract pos width i = Int.zero),
    Int.unsigned_bitfield_extract 0 pos i = i.
Proof.
  intros.
  apply Int.same_bits_eq; intros.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  rewrite ! Z.add_0_r.
  destruct zlt as [Hc | Hc]; [reflexivity|].
  symmetry.

  rewrite Int.unsigned_bitfield_extract_by_shifts in Hhi; try lia.
  replace (Int.zwordsize - pos - width) with 0%Z in Hhi by lia.
  fold Int.zero in Hhi.
  rewrite Int.shl_zero in Hhi.
  replace (Int.zwordsize - width) with pos in Hhi by lia.

  apply Int.bits_size_2.
  rewrite <- same_bits_eq_iff in Hhi.

  specialize (Hhi i0 H).
  rewrite Int.bits_zero in Hhi.
  rewrite Int.bits_shru in Hhi; try lia.
  destruct zlt as [Hd | Hd].
  - apply Int.bits_size_3; try lia.
    admit.
  - rewrite Int.unsigned_repr in Hd.
    + Search Int.size.
  
  assert (Heq: forall i0 : Z,
      0 <= i0 < Int.zwordsize ->
      Int.testbit (Int.shru i (Int.repr pos)) i0 = false). {
    intros.
    specialize (Hhi _ H0).
    rewrite Int.bits_zero in Hhi.
    auto.
  }
  apply Int.bits_size_3 in Heq; try lia.

  destruct (Int.bits_size_1 i).
  - subst i.
    rewrite Int.size_zero. lia.
  - 
  unfold Int.size.
  Search Int.shru.
  apply Int.bits_size_3; try lia.
  intros i1 Hi1.
  Search (Int.testbit _ _ =false).
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt as [Hd | Hd].
  - reflexivity.
  - lia.
Qed. *)

Lemma unsigned_bitfield_extract_unchange:
  forall i pos width
    (Hrange: 0 < pos /\ 0 < width /\ pos+width <= Int.zwordsize),
    (Int.unsigned_bitfield_extract 0 width
        (Int.unsigned_bitfield_extract pos width i)) =
    (Int.unsigned_bitfield_extract pos width i).
Proof.
  intros.
  apply Int.same_bits_eq; intros.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  symmetry.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt as [Hc | Hc]; [| reflexivity].
  rewrite Z.add_0_r.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt; [| lia].
  reflexivity.
Qed.

Lemma unsigned_bitfield_extract_same:
  forall i width
    (Hrange: 0 < width /\ width <= Int.zwordsize),
    Int.unsigned_bitfield_extract 0 width
      (Int.unsigned_bitfield_extract 0 width i) =
    Int.unsigned_bitfield_extract 0 width i.
Proof.
  intros.
  apply Int.same_bits_eq; intros.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  symmetry.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt as [Hc | Hc]; [| reflexivity].
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  rewrite ! Z.add_0_r.
  destruct zlt as [Hd | Hd].
  - reflexivity.
  - lia.
Qed.

Lemma unsigned_bitfield_extract_extend:
  forall i pos width
    (Hrange: 0 < pos /\ 0 < width /\ pos+width <= Int.zwordsize),
    Int.bitfield_insert pos width
      (Int.unsigned_bitfield_extract 0 pos i)
      (Int.unsigned_bitfield_extract pos width i) =
    Int.unsigned_bitfield_extract 0 (pos+width) i.
Proof.
  intros.
  apply Int.same_bits_eq; intros.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  rewrite Z.add_0_r.
  rewrite Int.bits_bitfield_insert; try lia.
  destruct (_ && _) eqn: Hc.
  - rewrite Bool.andb_true_iff in Hc.
    rewrite <- zle_true_iff in Hc.
    rewrite <- zlt_true_iff in Hc.
    rewrite Int.bits_unsigned_bitfield_extract; try lia.
    replace (i0 - pos + pos) with i0 by lia.
    destruct zlt as [Hd | Hd].
    + destruct zlt as [He | He].
      * reflexivity.
      * lia.
    + destruct zlt as [He | He].
      * lia.
      * reflexivity.
  - rewrite Bool.andb_false_iff in Hc.
    rewrite <- zle_false_iff in Hc.
    rewrite <- zlt_false_iff in Hc.
    rewrite Int.bits_unsigned_bitfield_extract; try lia.
    rewrite Z.add_0_r.
    destruct zlt as [Hd | Hd].
    + destruct zlt as [He | He].
      * reflexivity.
      * lia.
    + destruct zlt as [He | He].
      * lia.
      * reflexivity.
Qed.

Lemma bitfield_insert_over_size_zero:
  forall i x pos width
    (Hrange: 0 <= pos /\ 0 < width /\ pos+width <= Int.zwordsize)
    (HZ: Int.size i <= x)
    (HZR: x <= pos),
      Int.bitfield_insert pos width i Int.zero = i.
Proof.
  intros.
  apply Int.same_bits_eq; intros.
  rewrite Int.bits_bitfield_insert; try lia.
  destruct (zle pos i0 && zlt i0 (pos + width)) eqn: Hc.
  2:{ reflexivity. }
  rewrite Int.bits_zero.
  symmetry.
  apply Int.bits_size_2.
  rewrite andb_true_iff in Hc.
  destruct Hc as (Hc1 & Hc2).

  rewrite <- zle_true_iff in Hc1.
  rewrite <- zlt_true_iff in Hc2.
  lia.
Qed.

Lemma unsigned_bitfield_extract_over_size:
  forall i x pos width
    (Hrange: 0 <= pos /\ 0 < width /\ pos+width <= Int.zwordsize)
    (HZ: Int.size i <= x)
    (HZR: x <= pos),
      Int.unsigned_bitfield_extract pos width i = Int.zero.
Proof.
  intros.
  apply Int.same_bits_eq; intros.
  rewrite Int.bits_zero.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt as [Hlt | Hlt].
  2:{ reflexivity. }
  apply Int.bits_size_2. lia.
Qed.

Lemma unsigned_bitfield_extract_bitfield_insert_same:
  forall pos width v i
    (Hrange: 0 <= pos /\ 0 < width /\ pos+width <= Int.zwordsize)
    (HLOW: Int.size v <= width),
  Int.unsigned_bitfield_extract pos width
    (Int.bitfield_insert pos width i v) = v.
Proof.
  intros.
  apply Int.same_bits_eq; intros.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt eqn: Hlt.
  2:{ rewrite Int.bits_size_2; try lia. }
  rewrite Int.bits_bitfield_insert; try lia.
  replace (i0 + pos - pos) with i0 by lia.
  assert (Heq: (if zle pos (i0 + pos) then true else false) = true). {
    apply zle_true.
    lia.
  }
  rewrite andb_if with (b := zle pos (i0 + pos)).
  unfold proj_sumbool.
  rewrite Heq; clear Heq.
  assert (Heq: (if zlt (i0 + pos) (pos + width) then true else false) = true). {
    apply zlt_true.
    lia.
  }
  rewrite Heq; clear Heq.
  f_equal.
Qed.

Lemma size_bitfield_insert:
  forall pos width k i v
    (Hrange: 0 <= pos /\ 0 < width /\ pos+width <= k)
    (HI: Int.size i <= k)
    (HS: Int.size v <= width),
    Int.size (Int.bitfield_insert pos width i v) <= k.
Proof.
  intros.
  eapply Int.bits_size_3; eauto.
  lia.
  intros.
  rewrite Int.bits_bitfield_insert; try lia.
  destruct zle as [Hle | Hle]; [| lia].
  destruct zlt as [Hlt | Hlt]; [lia |].
  simpl.
  apply Int.bits_size_2. lia.
Qed.

Lemma size_unsigned_bitfield_extract:
  forall pos width k i
    (Hrange: 0 <= pos /\ 0 < width /\ width <= k /\ pos + width <= Int.zwordsize),
    Int.size (Int.unsigned_bitfield_extract pos width i) <= k.
Proof.
  intros.
  eapply Int.bits_size_3; eauto.
  lia.
  intros.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt as [Hlt | Hlt]; [lia |].
  reflexivity.
Qed.

Lemma unsigned_bitfield_extract_low_same:
  forall width v
    (Hrange: 0 < width /\ width <= Int.zwordsize)
    (HLOW: Int.size v <= width),
    Int.unsigned_bitfield_extract 0 width v = v.
Proof.
  intros.
  apply Int.same_bits_eq; intros.
  repeat rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct Coqlib.zlt eqn: Hlt.
  2:{ rewrite Int.bits_size_2; try lia. }
  rewrite Z.add_0_r.
  f_equal.
Qed.

Lemma bitfield_insert_unsigned_bitfield_extract_same:
  forall i p v t pos width
    (Hrange: 0 <= pos /\ 0 < width /\ pos+width <= Int.zwordsize)
    (Hpre: Int.unsigned_bitfield_extract pos width p = v)
    (Hinsert: Int.bitfield_insert pos width i v = t),
      Int.unsigned_bitfield_extract pos width t = v.
Proof.
  intros.
  destruct Hrange as (Hrange0 & Hrange1 & Hrange2).
  subst.
  apply Int.same_bits_eq; intros.
  repeat rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt eqn: Hlt; [| reflexivity].
  rewrite Int.bits_bitfield_insert; try lia.
  unfold proj_sumbool.
  rewrite zle_true; [| lia].
  rewrite zlt_true; [| lia].
  simpl.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  rewrite Z.add_simpl_r.
  rewrite Hlt.
  reflexivity.
Qed.


Lemma bitfield_insert_unsigned_bitfield_extract_same_outside:
  forall i p v t pos0 pos1 width0 width1
    (Hrange: pos0+width0 <= pos1 \/ pos1+width1 <= pos0)
    (Hrange0: 0 <= pos0 /\ 0 < width0 /\ pos0+width0 <= Int.zwordsize)
    (Hrange1: 0 <= pos1 /\ 0 < width1 /\ pos1+width1 <= Int.zwordsize)
    (Hpre: Int.unsigned_bitfield_extract pos1 width1 i = v)
    (Hinsert: Int.bitfield_insert pos0 width0 i p = t),
      Int.unsigned_bitfield_extract pos1 width1 t = v.
Proof.
  intros.
  destruct Hrange0 as (Hrange0_0 & Hrange0_1 & Hrange0_2).
  destruct Hrange1 as (Hrange1_0 & Hrange1_1 & Hrange1_2).
  subst.
  apply Int.same_bits_eq; intros.
  repeat rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt; [| reflexivity].
  rewrite Int.bits_bitfield_insert; try lia.
  unfold proj_sumbool.
  destruct Hrange as [Hrange | Hrange].
  - (**r pos0 + width0 <= pos1 *)
    rewrite zle_true; [| lia].
    rewrite zlt_false; [| lia].
    simpl.
    reflexivity.
  - (**r pos1 + width1 <= pos0 *)
    rewrite zle_false; [| lia].
    rewrite zlt_true; [| lia].
    simpl.
    reflexivity.
Qed.


Lemma unsigned_bitfield_extract_unsigned_bitfield_extract_zero_outside:
  forall i v pos0 pos1 width0 width1
    (Hrange: pos0+width0 <= pos1)
    (Hrange0: 0 <= pos0 /\ 0 < width0 /\ pos0+width0 <= Int.zwordsize)
    (Hrange1: 0 <= pos1 /\ 0 < width1 /\ pos1+width1 <= Int.zwordsize)
    (Hpre: Int.unsigned_bitfield_extract pos0 width0 i = v),
      Int.unsigned_bitfield_extract pos1 width1 v = Int.zero.
Proof.
  intros.
  destruct Hrange0 as (Hrange0_0 & Hrange0_1 & Hrange0_2).
  destruct Hrange1 as (Hrange1_0 & Hrange1_1 & Hrange1_2).
  subst.
  apply Int.same_bits_eq; intros.
  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt; [| rewrite Int.bits_zero; reflexivity].

  rewrite Int.bits_unsigned_bitfield_extract; try lia.
  destruct zlt; rewrite Int.bits_zero; [lia | reflexivity].
Qed.

Lemma unsigned_bitfield_extract_range_low:
  forall i v pos width
    (Hrange: 0 <= pos /\ 0 < width /\ pos+width <= Int.zwordsize)
    (Hpre: Int.unsigned_bitfield_extract pos width i = v),
      0 <= Int.unsigned v <= (two_p width) - 1.
Proof.
  intros.
  destruct Hrange as (Hrange0 & Hrange1 & Hrange2).
  subst.
  split.
  - change 0 with (Int.unsigned Int.zero).
    apply Int.bits_le.
    intros.
    rewrite Int.bits_zero in *.
    intuition.
  - rewrite <- Int.unsigned_repr.
    + apply Int.bits_le.
      intros.
      rewrite Int.testbit_repr; [| assumption].
      rewrite Zbits.Ztestbit_two_p_m1; try lia.
      rewrite Int.bits_unsigned_bitfield_extract in H0; try lia.
      destruct zlt; lia.
    + assert (Hrange: 1 <= two_p width <= Int.modulus).
      * rewrite Int.modulus_power.
        split.
        { assert (Htwo_p:= two_p_strict width).
          assert (Hwidth: width >= 0) by lia.
          specialize (Htwo_p Hwidth).
          lia.
        }
        { apply two_p_monotone.
          lia.
        }
      * change Int.max_unsigned with 4294967295 in *.
        change Int.modulus with 4294967296 in *.
        lia.
Qed.

Lemma Int_unsigned_bitfield_extract_zero_ext_narrow:
  forall k m n v,
    0 <= m -> 0 <= k -> m + k <= n -> n <= 64 ->
    Int.unsigned_bitfield_extract k m (Int.zero_ext n v) = Int.unsigned_bitfield_extract k m v.
Proof.
  unfold Int.unsigned_bitfield_extract.
  intros.
  assert (Heq: n = n - k + Int.unsigned (Int.repr k)). {
    rewrite Int.unsigned_repr.
    lia.
    change Int.max_unsigned with 4294967295.
    lia.
  }
  rewrite Heq; clear Heq.
  rewrite Int.shru_zero_ext; [| lia].
  rewrite Int.zero_ext_narrow.
  reflexivity.
  lia.
Qed.