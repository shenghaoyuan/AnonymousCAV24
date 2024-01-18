From compcert.common Require Import Values Memory AST.
From compcert.lib Require Import Integers Maps.
From compcert.arm Require Import AsmSyntax ABinSem BinDecode Conventions1 Machregs.

From bpf.rbpf32 Require Import TSSyntax.
From bpf.jit Require Import Arm32Reg.

From Coq Require Import ZArith Arith Lia List ListSet.

Open Scope asm.
Global Transparent Archi.ptr64.
Import ListNotations.

Ltac listset_context_solver :=
  match goal with
  |  |-
    @In breg ?r (@set_add breg breg_eq ?r _) =>
    apply set_add_intro2; auto
  | HSUB : @In breg ?r ?ld_set |- @In breg ?r ?ld_set =>
    assumption
  | Hr_neq : not (@eq breg ?dst ?dst) |- _ =>
    exfalso; apply Hr_neq; reflexivity

  | H : @set_In breg _ _ |- _ =>
    unfold set_In in H
  | |- @set_In breg _ _ =>
    unfold set_In

  | H: @In breg ?r (@set_union breg breg_eq ?X ?Y) |- _ =>
    apply set_union_elim in H; destruct H as [H | H]
  | H: @In breg ?r (@set_add breg breg_eq ?X ?Y) |- _ =>
    apply set_add_elim in H; destruct H as [H | H]
  | H: @eq breg ?x ?y |- _ =>
    subst x

  | Hr_neq : not (@eq breg ?r ?dst),
    H : @In breg ?r (@set_add breg breg_eq ?dst _) |- _ =>
      apply set_add_elim in H; destruct H as [H | H]; [exfalso; apply Hr_neq; auto |]
  | H : @In breg ?r ?ld_set |-
    @In breg ?r (@set_union breg breg_eq ?ld_set _) =>
      apply set_union_intro1; auto
  | H : @In breg ?r ?ld_set |-
    @In breg ?r (@set_union breg breg_eq _ ?ld_set) =>
      apply set_union_intro1; auto


  | HN : not (@In breg ?r _) |-
    not (@In breg ?r _) =>
      intro HF; apply HN


  | H: @In breg ?r _ |-
    @In breg ?r (@set_add breg breg_eq ?y _) =>
      apply set_add_intro1

  | HSUB : forall (r : breg) (_ : @In breg r ?st_set), @In breg r ?ld_set,
    H: @In breg ?r ?st_set |-
    @In breg ?r (@set_add breg breg_eq ?y ?ld_set) =>
      specialize (HSUB _ H); apply set_add_intro1
  | H : @In breg ?r ?st_set,
    HSUB : forall (r : breg) (_ : @In breg r ?st_set), @In breg r ?ld_set |-
    @In breg ?r ?ld_set =>
      apply HSUB; auto

  | HF : @In breg ?r ?ld_set |-
    @In breg ?r (@set_union breg breg_eq ?X ?Y) =>
      try (apply set_union_intro1; listset_context_solver);
      try (apply set_union_intro2; listset_context_solver)
  end.

Ltac in_listset_solver :=
  match goal with
  | |- @In breg ?r (@set_union breg breg_eq ?X ?Y) =>
    try (apply set_union_intro2; in_listset_solver);
      apply set_union_intro1
  | |- @set_In breg ?r (@set_union breg breg_eq ?X ?Y) =>
    try (apply set_union_intro2; in_listset_solver);
      apply set_union_intro1

  | |- @In breg ?r (@set_add breg breg_eq ?r ?Y) =>
    apply set_add_intro2; auto
  | |- @set_In breg ?r (@set_add breg breg_eq ?r ?Y) =>
    apply set_add_intro2; auto

  | |- @In breg ?r (@set_add breg breg_eq ?y ?Y) =>
    apply set_add_intro1; in_listset_solver
  | |- @set_In breg ?r (@set_add breg breg_eq ?y ?Y) =>
    apply set_add_intro1; in_listset_solver
  end.

Ltac listset_solver := repeat in_listset_solver; repeat listset_context_solver.

Ltac abreg_solver :=
  match goal with
  | |- @eq aval (@Pregmap.set aval PC _ _ (IR (ireg_of_breg ?R))) _ =>
    rewrite Pregmap.gso; [| intro HF; inversion HF]
  | |- @eq aval (@Pregmap.set aval (IR (ireg_of_breg ?R)) ?V _ (IR (ireg_of_breg ?R))) ?V =>
    rewrite Pregmap.gss; reflexivity
  | |- @eq aval (@Pregmap.set aval (IR (ireg_of_breg ?R)) _ _ (IR IR12)) _ =>
    rewrite Pregmap.gso; [| unfold ireg_of_breg; destruct R; intro HF; inversion HF]
  | |- @eq aval (@Pregmap.set aval (IR (ireg_of_breg ?R)) _ _ (IR IR13)) _ =>
    rewrite Pregmap.gso; [| unfold ireg_of_breg; destruct R; intro HF; inversion HF]
  | |- @eq aval (@Pregmap.set aval (IR (ireg_of_breg ?R)) _ _ (IR IR14)) _ =>
    rewrite Pregmap.gso; [| unfold ireg_of_breg; destruct R; intro HF; inversion HF]
  | |- @eq aval (@Pregmap.set aval PC _ _ (IR ?R)) _ =>
    rewrite Pregmap.gso; [| intro HF; inversion HF]
  | |- @eq aval (@Pregmap.set aval (IR IR11) _ _  (IR IR12)) _ =>
    rewrite Pregmap.gso; [| intro HF; inversion HF]
  | |- @eq aval (@Pregmap.set aval (IR IR11) _ _  (IR IR13)) _ =>
    rewrite Pregmap.gso; [| intro HF; inversion HF]
  | |- @eq aval (@Pregmap.set aval (IR IR11) _ _  (IR IR14)) _ =>
    rewrite Pregmap.gso; [| intro HF; inversion HF]

  | |- @eq val (@BPregmap.set val BPC _ _ (BR ?R)) _ =>
    rewrite BPregmap.gso; [| intro HF; inversion HF]
  | |- @eq val (@BPregmap.set val (BR ?R) ?V _ (BR ?R)) ?V =>
    rewrite BPregmap.gss; reflexivity
  | H: not (@eq breg ?X ?Y) |- @eq val (@BPregmap.set val (BR ?Y) _ _ (BR ?X)) _ =>
    rewrite BPregmap.gso; [| intro HF; apply H; inversion HF; reflexivity]

  | H: not (@eq breg ?X ?Y) |- @eq aval (@Pregmap.set aval (IR (ireg_of_breg ?Y)) _ _ (IR (ireg_of_breg ?X))) _ =>
    rewrite Pregmap.gso;
      [| unfold ireg_of_breg; destruct X; destruct Y;
          intro HF; apply H; inversion HF; auto]
  | H : not (@eq breg ?X ?Y) |- @eq aval (@Pregmap.set aval (IR (ireg_of_breg ?Y)) _ _ (IR (ireg_of_breg ?X))) _ =>
    rewrite Pregmap.gso; [ |
      unfold ireg_of_breg; intro HF; apply H;
      destruct X; destruct Y; inversion HF; auto]

  | |- @eq aval (@Pregmap.set aval (IR IR11) _ _ (IR (ireg_of_breg ?X))) _ =>
    rewrite Pregmap.gso;
      [| unfold ireg_of_breg; destruct X; intro HF; inversion HF]


  | |- @eq val (?X (BR ?R)) (?X (BR ?R)) => reflexivity
  | H: ?X |- ?X => assumption
  | |- ?X = ?X => reflexivity

  | |- context[(@Pregmap.set aval (IR (ireg_of_breg ?R)) _ _ (IR (ireg_of_breg ?R)))] =>
    rewrite Pregmap.gss
  end.

Ltac abreg_solver_error_prone := (**r this may be wrong *)
  match goal with
  | H : not (@eq breg ?Y ?X) |- context[(@Pregmap.set aval (IR (ireg_of_breg ?X)) _ _ (IR (ireg_of_breg ?Y)))] =>
    rewrite Pregmap.gso;
      [| unfold ireg_of_breg; destruct X; destruct Y;
          intro HF; apply H; inversion HF; auto]
  | H : not (@eq breg ?X ?Y) |- context[(@Pregmap.set aval (IR (ireg_of_breg ?X)) _ _ (IR (ireg_of_breg ?Y)))] =>
    rewrite Pregmap.gso;
      [| unfold ireg_of_breg; destruct X; destruct Y;
          intro HF; apply H; inversion HF; auto]
  | |- context[@Pregmap.set aval (IR (ireg_of_breg ?X)) _ _ (IR IR12)] =>
    rewrite Pregmap.gso; [| unfold ireg_of_breg; destruct X; intro HF; inversion HF]
  | |- context[@Pregmap.set aval (IR (ireg_of_breg ?X)) _ _ (IR IR13)] =>
    rewrite Pregmap.gso; [| unfold ireg_of_breg; destruct X; intro HF; inversion HF]
  | |- context[@Pregmap.set aval (IR (ireg_of_breg ?R)) _ _ (IR (ireg_of_breg ?R))] =>
    rewrite Pregmap.gss

  | |- context[(@Pregmap.set aval (IR IR11) _ _ (IR (ireg_of_breg ?dst)))] =>
    rewrite Pregmap.gso;
      [| unfold ireg_of_breg; destruct dst; intro HF; inversion HF]
  | |- context[(@Pregmap.set aval (IR ?X) _ _ (IR ?X))] =>
    rewrite Pregmap.gss

  | |- context[(@Pregmap.set aval PC _ _ PC)] =>
    rewrite Pregmap.gss
  | |- context[(@Pregmap.set aval PC _ _ (IR ?R))] =>
    rewrite Pregmap.gso; [| intro HF; inversion HF]
  end.

Ltac float_preg_of_solver :=
  match goal with
  | H: @In mreg ?x float_callee_save_regs
    |- context [(@Pregmap.set aval _ _ _ (preg_of ?x))] =>
      rewrite Pregmap.gso; [ |
        repeat (destruct H as [H | H];
          [subst x; intro HF; inversion HF|]); inversion H ]
  end.


Ltac decode_val_same_breg_solver :=
  match goal with
  | |- @eq (option aval) (decode_val Many32
    (encode_sval_fragments Cany32 (Rval (Sreg (IR (ireg_of_breg ?R))))))
    (@Some aval (Aval (Rval (Sreg (IR (ireg_of_breg ?R)))))) =>
    unfold decode_val; simpl;
    unfold proj_value, rchunk_of_chunk;
    destruct (Coqlib.proj_sumbool (rchunk_eq Cany32 Cany32)) eqn: Heq;
      [clear Heq | inversion Heq];
    unfold check_value;
    destruct (Coqlib.proj_sumbool (rchunk_eq Cany32 Cany32)) eqn: Heq;
      [clear Heq | inversion Heq];
    unfold sval_eq, sreg_eq;
    destruct (preg_eq _ _) as [Heq | Hneq];
      [ | exfalso; apply Hneq; reflexivity];
    simpl;
    f_equal
  end.

Ltac prove_int :=
  match goal with
  | |- context[Int.size ?X] => let v := (eval vm_compute in (Int.size X)) in
        replace (Int.size X) with v by reflexivity; lia
  | |- context[Int.unsigned (Int.repr ?X)] => let v := (eval vm_compute in (Int.unsigned (Int.repr X))) in
        replace (Int.unsigned (Int.repr X)) with v by reflexivity; try lia
  | |- context[Ptrofs.unsigned (Ptrofs.repr ?X)] => let v := (eval vm_compute in (Ptrofs.unsigned (Ptrofs.repr X))) in
        replace (Ptrofs.unsigned (Ptrofs.repr X)) with v by reflexivity; try lia
  | |- context[Int.lt (Int.repr ?X) (Int.repr ?Y)] => let v := (eval vm_compute in (Int.lt (Int.repr X) (Int.repr Y))) in
        replace (Int.lt (Int.repr X) (Int.repr Y)) with v by reflexivity; try lia
  end.

Ltac prove_int_bit :=
  match goal with
  | |- context[Int.bitfield_insert ?X ?Y ?Z ?K] => let v := (eval vm_compute in (Int.bitfield_insert X Y Z K)) in
        replace (Int.bitfield_insert X Y Z K) with v by reflexivity; try lia
  end.

Ltac int_true_false :=
  match goal with
  | |- context [Int.lt ?X ?Y]  => let v := (eval vm_compute in (Int.lt X Y)) in
        replace (Int.lt X Y) with v by reflexivity; simpl
  | |- context [Int.eq ?X ?Y]  => let v := (eval vm_compute in (Int.eq X Y)) in
        replace (Int.eq X Y) with v by reflexivity; simpl
  | |- context [Int.unsigned_bitfield_extract ?X ?Y ?Z]  =>
    let v := (eval vm_compute in (Int.unsigned_bitfield_extract X Y Z)) in
        replace (Int.unsigned_bitfield_extract X Y Z) with v by reflexivity; simpl; reflexivity
  | |- context [Int.bitfield_insert ?X ?Y ?Z ?K]  =>
    let v := (eval vm_compute in (Int.bitfield_insert X Y Z K)) in
        replace (Int.bitfield_insert X Y Z K) with v by reflexivity; simpl; reflexivity
  end.

Lemma int_ltu_0:
  forall x,
  Int.ltu x Int.zero = false.
Proof.
  intros.
  unfold Int.ltu.
  destruct Coqlib.zlt.
  - rewrite Int.unsigned_zero in *.
    assert (H: (0 <= Int.unsigned x <= Int.max_unsigned)%Z) by apply Int.unsigned_range_2.
    lia.
  - reflexivity.
Qed.

Lemma int_ltu_4095_mul_breg_4:
  forall br,
  Int.ltu (Int.repr 4095) (Int.mul (int_of_breg br) (Int.repr 4)) = false.
Proof.
  intros; destruct br; unfold int_of_breg; auto.
Qed.

Lemma int2ireg_int_of_ireg_same:
  forall ir,
    int2ireg (int_of_ireg ir) = Some ir.
Proof.
  unfold int2ireg, int_of_ireg.
  intros; destruct ir; simpl; auto.
Qed.


Lemma int2ireg_int_of_breg_same:
  forall br,
    int2ireg (int_of_breg br) = Some (ireg_of_breg br).
Proof.
  unfold int2ireg, int_of_breg, ireg_of_breg.
  intros; destruct br; simpl; auto.
Qed.