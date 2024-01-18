From bpf.rbpf32 Require Import TSSyntax.

From Coq Require Import List ZArith.
Import ListNotations.
Open Scope bool_scope.

Record listset_regmap: Type := {
  r0_b  : bool;
  r1_b  : bool;
  r2_b  : bool;
  r3_b  : bool;
  r4_b  : bool;
  r5_b  : bool;
  r6_b  : bool;
  r7_b  : bool;
  r8_b  : bool;
  r9_b  : bool;
  r10_b : bool;
}.

Definition eval_listset_regmap (r: breg) (regs: listset_regmap): bool := 
  match r with
  | R0  => r0_b regs
  | R1  => r1_b regs
  | R2  => r2_b regs
  | R3  => r3_b regs
  | R4  => r4_b regs
  | R5  => r5_b regs
  | R6  => r6_b regs
  | R7  => r7_b regs
  | R8  => r8_b regs
  | R9  => r9_b regs
  | R10 => r10_b regs
  end.

Definition upd_listset_regmap (r: breg) (regs: listset_regmap): listset_regmap :=
  match r with
  | R0  => 
    {|
      r0_b  := true;
      r1_b  := r1_b regs;
      r2_b  := r2_b regs;
      r3_b  := r3_b regs;
      r4_b  := r4_b regs;
      r5_b  := r5_b regs;
      r6_b  := r6_b regs;
      r7_b  := r7_b regs;
      r8_b  := r8_b regs;
      r9_b  := r9_b regs;
      r10_b := r10_b regs;
    |} 
  | R1  =>
    {|
      r0_b  := r0_b regs;
      r1_b  := true;
      r2_b  := r2_b regs;
      r3_b  := r3_b regs;
      r4_b  := r4_b regs;
      r5_b  := r5_b regs;
      r6_b  := r6_b regs;
      r7_b  := r7_b regs;
      r8_b  := r8_b regs;
      r9_b  := r9_b regs;
      r10_b := r10_b regs;
    |}
  | R2  => 
    {|
      r0_b  := r0_b regs;
      r1_b  := r1_b regs;
      r2_b  := true;
      r3_b  := r3_b regs;
      r4_b  := r4_b regs;
      r5_b  := r5_b regs;
      r6_b  := r6_b regs;
      r7_b  := r7_b regs;
      r8_b  := r8_b regs;
      r9_b  := r9_b regs;
      r10_b := r10_b regs;
    |} 
  | R3  => 
    {|
      r0_b  := r0_b regs;
      r1_b  := r1_b regs;
      r2_b  := r2_b regs;
      r3_b  := true;
      r4_b  := r4_b regs;
      r5_b  := r5_b regs;
      r6_b  := r6_b regs;
      r7_b  := r7_b regs;
      r8_b  := r8_b regs;
      r9_b  := r9_b regs;
      r10_b := r10_b regs;
    |} 
  | R4  => 
    {|
      r0_b  := r0_b regs;
      r1_b  := r1_b regs;
      r2_b  := r2_b regs;
      r3_b  := r3_b regs;
      r4_b  := true;
      r5_b  := r5_b regs;
      r6_b  := r6_b regs;
      r7_b  := r7_b regs;
      r8_b  := r8_b regs;
      r9_b  := r9_b regs;
      r10_b := r10_b regs;
    |} 
  | R5  => 
    {|
      r0_b  := r0_b regs;
      r1_b  := r1_b regs;
      r2_b  := r2_b regs;
      r3_b  := r3_b regs;
      r4_b  := r4_b regs;
      r5_b  := true;
      r6_b  := r6_b regs;
      r7_b  := r7_b regs;
      r8_b  := r8_b regs;
      r9_b  := r9_b regs;
      r10_b := r10_b regs;
    |} 
  | R6  => 
    {|
      r0_b  := r0_b regs;
      r1_b  := r1_b regs;
      r2_b  := r2_b regs;
      r3_b  := r3_b regs;
      r4_b  := r4_b regs;
      r5_b  := r5_b regs;
      r6_b  := true;
      r7_b  := r7_b regs;
      r8_b  := r8_b regs;
      r9_b  := r9_b regs;
      r10_b := r10_b regs;
    |} 
  | R7  => 
    {|
      r0_b  := r0_b regs;
      r1_b  := r1_b regs;
      r2_b  := r2_b regs;
      r3_b  := r3_b regs;
      r4_b  := r4_b regs;
      r5_b  := r5_b regs;
      r6_b  := r6_b regs;
      r7_b  := true;
      r8_b  := r8_b regs;
      r9_b  := r9_b regs;
      r10_b := r10_b regs;
    |} 
  | R8  => 
    {|
      r0_b  := r0_b regs;
      r1_b  := r1_b regs;
      r2_b  := r2_b regs;
      r3_b  := r3_b regs;
      r4_b  := r4_b regs;
      r5_b  := r5_b regs;
      r6_b  := r6_b regs;
      r7_b  := r7_b regs;
      r8_b  := true;
      r9_b  := r9_b regs;
      r10_b := r10_b regs;
    |} 
  | R9  => 
    {|
      r0_b  := r0_b regs;
      r1_b  := r1_b regs;
      r2_b  := r2_b regs;
      r3_b  := r3_b regs;
      r4_b  := r4_b regs;
      r5_b  := r5_b regs;
      r6_b  := r6_b regs;
      r7_b  := r7_b regs;
      r8_b  := r8_b regs;
      r9_b  := true;
      r10_b := r10_b regs;
    |} 
  | R10 => 
    {|
      r0_b  := r0_b regs;
      r1_b  := r1_b regs;
      r2_b  := r2_b regs;
      r3_b  := r3_b regs;
      r4_b  := r4_b regs;
      r5_b  := r5_b regs;
      r6_b  := r6_b regs;
      r7_b  := r7_b regs;
      r8_b  := r8_b regs;
      r9_b  := r9_b regs;
      r10_b := true;
    |} 
  end.

Definition reset_listset_regmap (r: breg) (regs: listset_regmap): listset_regmap :=
  match r with
  | R0  => 
    {|
      r0_b  := false;
      r1_b  := r1_b regs;
      r2_b  := r2_b regs;
      r3_b  := r3_b regs;
      r4_b  := r4_b regs;
      r5_b  := r5_b regs;
      r6_b  := r6_b regs;
      r7_b  := r7_b regs;
      r8_b  := r8_b regs;
      r9_b  := r9_b regs;
      r10_b := r10_b regs;
    |} 
  | R1  =>
    {|
      r0_b  := r0_b regs;
      r1_b  := false;
      r2_b  := r2_b regs;
      r3_b  := r3_b regs;
      r4_b  := r4_b regs;
      r5_b  := r5_b regs;
      r6_b  := r6_b regs;
      r7_b  := r7_b regs;
      r8_b  := r8_b regs;
      r9_b  := r9_b regs;
      r10_b := r10_b regs;
    |}
  | R2  => 
    {|
      r0_b  := r0_b regs;
      r1_b  := r1_b regs;
      r2_b  := false;
      r3_b  := r3_b regs;
      r4_b  := r4_b regs;
      r5_b  := r5_b regs;
      r6_b  := r6_b regs;
      r7_b  := r7_b regs;
      r8_b  := r8_b regs;
      r9_b  := r9_b regs;
      r10_b := r10_b regs;
    |} 
  | R3  => 
    {|
      r0_b  := r0_b regs;
      r1_b  := r1_b regs;
      r2_b  := r2_b regs;
      r3_b  := false;
      r4_b  := r4_b regs;
      r5_b  := r5_b regs;
      r6_b  := r6_b regs;
      r7_b  := r7_b regs;
      r8_b  := r8_b regs;
      r9_b  := r9_b regs;
      r10_b := r10_b regs;
    |} 
  | R4  => 
    {|
      r0_b  := r0_b regs;
      r1_b  := r1_b regs;
      r2_b  := r2_b regs;
      r3_b  := r3_b regs;
      r4_b  := false;
      r5_b  := r5_b regs;
      r6_b  := r6_b regs;
      r7_b  := r7_b regs;
      r8_b  := r8_b regs;
      r9_b  := r9_b regs;
      r10_b := r10_b regs;
    |} 
  | R5  => 
    {|
      r0_b  := r0_b regs;
      r1_b  := r1_b regs;
      r2_b  := r2_b regs;
      r3_b  := r3_b regs;
      r4_b  := r4_b regs;
      r5_b  := false;
      r6_b  := r6_b regs;
      r7_b  := r7_b regs;
      r8_b  := r8_b regs;
      r9_b  := r9_b regs;
      r10_b := r10_b regs;
    |} 
  | R6  => 
    {|
      r0_b  := r0_b regs;
      r1_b  := r1_b regs;
      r2_b  := r2_b regs;
      r3_b  := r3_b regs;
      r4_b  := r4_b regs;
      r5_b  := r5_b regs;
      r6_b  := false;
      r7_b  := r7_b regs;
      r8_b  := r8_b regs;
      r9_b  := r9_b regs;
      r10_b := r10_b regs;
    |} 
  | R7  => 
    {|
      r0_b  := r0_b regs;
      r1_b  := r1_b regs;
      r2_b  := r2_b regs;
      r3_b  := r3_b regs;
      r4_b  := r4_b regs;
      r5_b  := r5_b regs;
      r6_b  := r6_b regs;
      r7_b  := false;
      r8_b  := r8_b regs;
      r9_b  := r9_b regs;
      r10_b := r10_b regs;
    |} 
  | R8  => 
    {|
      r0_b  := r0_b regs;
      r1_b  := r1_b regs;
      r2_b  := r2_b regs;
      r3_b  := r3_b regs;
      r4_b  := r4_b regs;
      r5_b  := r5_b regs;
      r6_b  := r6_b regs;
      r7_b  := r7_b regs;
      r8_b  := false;
      r9_b  := r9_b regs;
      r10_b := r10_b regs;
    |} 
  | R9  => 
    {|
      r0_b  := r0_b regs;
      r1_b  := r1_b regs;
      r2_b  := r2_b regs;
      r3_b  := r3_b regs;
      r4_b  := r4_b regs;
      r5_b  := r5_b regs;
      r6_b  := r6_b regs;
      r7_b  := r7_b regs;
      r8_b  := r8_b regs;
      r9_b  := false;
      r10_b := r10_b regs;
    |} 
  | R10 => 
    {|
      r0_b  := r0_b regs;
      r1_b  := r1_b regs;
      r2_b  := r2_b regs;
      r3_b  := r3_b regs;
      r4_b  := r4_b regs;
      r5_b  := r5_b regs;
      r6_b  := r6_b regs;
      r7_b  := r7_b regs;
      r8_b  := r8_b regs;
      r9_b  := r9_b regs;
      r10_b := false;
    |} 
  end.

(**r the value is 32-bit *)
Definition init_listset_regmap: listset_regmap := {|
  r0_b  := false;
  r1_b  := false;
  r2_b  := false;
  r3_b  := false;
  r4_b  := false;
  r5_b  := false;
  r6_b  := false;
  r7_b  := false;
  r8_b  := false;
  r9_b  := false;
  r10_b := false;
|}.

Definition listset_add_regmap (r: breg) (rs: listset_regmap): listset_regmap :=
  if eval_listset_regmap r rs then
    rs
  else
    upd_listset_regmap r rs.

Lemma eval_upd_listset_regmap:
  forall r st,
    eval_listset_regmap r (listset_add_regmap r st) = true.
Proof.
  intros.
  unfold listset_add_regmap, eval_listset_regmap, upd_listset_regmap.
  destruct r; simpl;
  match goal with
  | |- context [if ?X then _ else _] =>
    destruct X eqn: Heq; [simpl |]; auto
  end.
Qed.

Lemma eval_upd_listset_regmap_other:
  forall r r0 st,
    r <> r0 ->
    eval_listset_regmap r (listset_add_regmap r0 st) = eval_listset_regmap r st.
Proof.
  intros.
  unfold listset_add_regmap, eval_listset_regmap, upd_listset_regmap.
  destruct r; destruct r0;
  match goal with
  | H : ?R <> ?Y |- context [if ?X then _ else _] =>
    destruct X eqn: Heq; [auto|
      try (simpl; reflexivity); exfalso; apply H; reflexivity]
  end.
Qed.

Lemma eval_upd_reset_listset_regmap_same:
  forall l a,
    eval_listset_regmap a l = true ->
      upd_listset_regmap a (reset_listset_regmap a l) = l.
Proof.
  unfold reset_listset_regmap, eval_listset_regmap, upd_listset_regmap;
  intros l a H;
  destruct a;
  simpl; rewrite <- H; destruct l; simpl; reflexivity.
Qed.

Lemma eval_listset_regmap_reset_listset_regmap_same:
  forall r l,
  eval_listset_regmap r (reset_listset_regmap r l) = false.
Proof.
  intros.
  unfold eval_listset_regmap, reset_listset_regmap;
  destruct r; simpl; reflexivity.
Qed.

Lemma eval_listset_regmap_reset_listset_regmap_other:
  forall r r' l,
  r <> r' ->
  eval_listset_regmap r (reset_listset_regmap r' l) = eval_listset_regmap r l.
Proof.
  intros.
  unfold eval_listset_regmap, reset_listset_regmap;
  destruct r; destruct r';
  match goal with
  | H : ?R <> ?R |- _ =>
    exfalso; apply H; reflexivity
  | H : ?R <> ?Y |- _ =>
    simpl; reflexivity
  end.
Qed.