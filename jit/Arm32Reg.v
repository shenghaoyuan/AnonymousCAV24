From compcert.lib Require Import Integers.
From compcert.arm Require Import AsmSyntax.

From bpf.rbpf32 Require Import TSSyntax.

From Coq Require Import ZArith.

Definition ireg_eqb (r0 r1: ireg): bool :=
  match r0, r1 with
  | IR0, IR0
  | IR1, IR1
  | IR2, IR2
  | IR3, IR3
  | IR4, IR4
  | IR5, IR5
  | IR6, IR6
  | IR7, IR7
  | IR8, IR8
  | IR9, IR9
  | IR10, IR10
  | IR11, IR11
  | IR12, IR12
  | IR13, IR13
  | IR14, IR14 => true
  | _, _ => false
  end.

Definition reg_ireg_eqb (r0: breg) (r1: ireg): bool :=
  match r0, r1 with
  | R0, IR0
  | R1, IR1
  | R2, IR2
  | R3, IR3
  | R4, IR4
  | R5, IR5
  | R6, IR6
  | R7, IR7
  | R8, IR8
  | R9, IR9
  | R10, IR10 => true
  | _, _ => false
  end.


Definition breg_of_ireg (r: ireg): option breg :=
  match r with
  | IR0 => Some R0
  | IR1 => Some R1
  | IR2 => Some R2
  | IR3 => Some R3
  | IR4 => Some R4
  | IR5 => Some R5
  | IR6 => Some R6
  | IR7 => Some R7
  | IR8 => Some R8
  | IR9 => Some R9
  | IR10 => Some R10
  | IR11
  | IR12
  | IR13
  | IR14 => None
  end.

Definition ireg_of_breg (r: breg): ireg :=
  match r with
  | R0 => IR0
  | R1 => IR1
  | R2 => IR2
  | R3 => IR3
  | R4 => IR4
  | R5 => IR5
  | R6 => IR6
  | R7 => IR7
  | R8 => IR8
  | R9 => IR9
  | R10 => IR10
  end.


Definition ireg2nat (r: ireg): nat :=
  match r with
  | IR0 => 0
  | IR1 => 1
  | IR2 => 2
  | IR3 => 3
  | IR4 => 4
  | IR5 => 5
  | IR6 => 6
  | IR7 => 7
  | IR8 => 8
  | IR9 => 9
  | IR10 => 10
  | IR11 => 11
  | IR12 => 12
  | IR13 => 13
  | IR14 => 14
  end.


Definition Z_of_ireg (r: ireg): Z :=
  match r with
  | IR0 => 0
  | IR1 => 1
  | IR2 => 2
  | IR3 => 3
  | IR4 => 4
  | IR5 => 5
  | IR6 => 6
  | IR7 => 7
  | IR8 => 8
  | IR9 => 9
  | IR10 => 10
  | IR11 => 11
  | IR12 => 12
  | IR13 => 13
  | IR14 => 14
  end.

Definition int_of_ireg (r: ireg): int := Int.repr (Z_of_ireg r).

Definition int16_of_ireg (r: ireg): int := Int.repr (Z_of_ireg r).

Lemma ireg_eqb_true:
  forall x y, x = y <-> ireg_eqb x y = true.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

Lemma ireg_eqb_false:
  forall x y, x <> y <-> ireg_eqb x y = false.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

Lemma ireg_of_reg_eq:
  forall r0 r1,
    ireg_of_breg r0 = ireg_of_breg r1 -> r0 = r1.
Proof.
  intros.
  unfold ireg_of_breg in H.
  destruct r0; destruct r1; inversion H.
  all: reflexivity.
Qed.

Lemma ireg_of_breg_neq:
  forall x y, x <> y <-> ireg_of_breg x <> ireg_of_breg y.
Proof.
  intros x y.
  split; intros Hneq HF; apply Hneq.
  - destruct x; destruct y; inversion HF; reflexivity.
  - rewrite HF. f_equal.
Qed.

Lemma ireg_of_breg_eq:
  forall x y, x = y <-> ireg_of_breg x = ireg_of_breg y.
Proof.
  intros x y.
  split; intros Heq.
  - rewrite Heq. f_equal.
  - destruct x; destruct y; inversion Heq; reflexivity.
Qed.

Lemma reg_ireg_eqb_ireg_of_breg_true:
  forall x y,
    reg_ireg_eqb x (ireg_of_breg y) = true <-> x = y.
Proof.
  unfold reg_ireg_eqb, ireg_of_breg; intros.
  split; intro Heq.
  - destruct x; destruct y; inversion Heq; reflexivity.
  - rewrite Heq. destruct y; reflexivity.
Qed.

Lemma reg_ireg_eqb_ireg_of_breg_false:
  forall x y,
    reg_ireg_eqb x (ireg_of_breg y) = false <-> x <> y.
Proof.
  intros.
  split; intro Heq.
  - destruct x; destruct y; inversion Heq; intro HF; inversion HF.
  - apply Bool.not_true_is_false. intro HF; apply Heq. apply reg_ireg_eqb_ireg_of_breg_true; auto.
Qed.