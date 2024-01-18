From compcert.common Require Import Values Memory AST.
From compcert.lib Require Import Integers.
From compcert.arm Require Import ABinSem.

From bpf.comm Require Import JITCall.
From bpf.rbpf32 Require Import JITConfig TSSyntax. (* TSSemanticsJIT
From bpf.jit Require Import ThumbJITProofSubMem. *)
From bpf.jit Require Import ThumbJITLtac.

From Coq Require Import List ZArith Arith String Lia Logic.FunctionalExtensionality.
Open Scope nat_scope.
Open Scope asm.
Import ListNotations.

Lemma int_unsigned_repr_int:
  forall r,
    Int.unsigned (int_of_breg r) = z_of_breg r.
Proof.
  intros.
  unfold int_of_breg.
  rewrite Int.unsigned_repr.
  2:{
    change Int.max_unsigned with 4294967295%Z.
    unfold z_of_breg; destruct r; simpl; repeat prove_int; lia.
  }
  f_equal.
Qed.

Lemma int_mul_4:
  forall r,
  Int.unsigned (Int.mul (int_of_breg r) (Int.repr 4)) =
  ((z_of_breg r) * 4)%Z.
Proof.
  unfold Int.mul.
  intros.
  rewrite Int.unsigned_repr.
  2:{
    change Int.max_unsigned with 4294967295%Z.
    unfold int_of_breg; destruct r; simpl; repeat prove_int.
  }
  prove_int.
  rewrite <- int_unsigned_repr_int.
  f_equal.
Qed.

Lemma ptr_int_mul_4:
  forall r,
  Ptrofs.unsigned (Ptrofs.of_int (Int.mul (int_of_breg r) (Int.repr 4))) =
  ((z_of_breg r) * 4)%Z.
Proof.
  unfold Ptrofs.of_int.
  intros.
  rewrite int_mul_4.
  rewrite Ptrofs.unsigned_repr.
  2:{
    change Ptrofs.max_unsigned with 4294967295%Z.
    unfold z_of_breg; destruct r; simpl; lia.
  }
  f_equal.
Qed.


Lemma reg_lt_true_l:
  forall i r, (0 <= i < 16)%Z -> Int.ltu (Int.repr i) (int_of_breg r) = true -> (i < (z_of_breg r))%Z.
Proof.
  unfold int_of_breg, z_of_breg.
  intros i r Hc Hlt.
  eapply Int.ltu_inv in Hlt.
  rewrite Int.unsigned_repr in Hlt.
  2:{ change Int.max_unsigned with 4294967295%Z; lia. }
  rewrite Int.unsigned_repr in Hlt.
  2:{ change Int.max_unsigned with 4294967295%Z; destruct r; lia. }
  lia.
Qed.

Lemma reg_lt_true_r:
  forall i r, (0 <= i < 16)%Z -> Int.ltu (int_of_breg r) (Int.repr i) = true -> ((z_of_breg r)< i)%Z.
Proof.
  unfold int_of_breg, z_of_breg.
  intros i r Hc Hlt.
  eapply Int.ltu_inv in Hlt.
  rewrite Int.unsigned_repr in Hlt.
  2:{ change Int.max_unsigned with 4294967295%Z; destruct r; lia. }
  rewrite Int.unsigned_repr in Hlt.
  2:{ change Int.max_unsigned with 4294967295%Z; lia. }
  lia.
Qed.

Lemma zeq_true:
  forall (A : Type) (x y: Z) (a b : A), (a <> b) -> (if Coqlib.zeq x y then a else b) = a -> x = y.
Proof.
  intros.
  unfold Coqlib.zeq in H. destruct Z.eq_dec.
  lia.
  exfalso.
  apply H.
  auto.
Qed.

Lemma reg_lt_false_l:
  forall i r, (0 <= i < 16)%Z -> Int.ltu (Int.repr i) (int_of_breg r) = false -> (i >= (z_of_breg r))%Z.
Proof.
  unfold int_of_breg, z_of_breg.
  intros i r Hc Hlt.
  rewrite <- Bool.negb_true_iff in Hlt.
  rewrite Int.not_ltu in Hlt.
  rewrite Bool.orb_true_iff in Hlt.
  destruct Hlt as [HL | HE].
  - eapply Int.ltu_inv in HL.
    rewrite Int.unsigned_repr in HL.
    2:{ change Int.max_unsigned with 4294967295%Z; destruct r; lia. }
    rewrite Int.unsigned_repr in HL.
    2:{ change Int.max_unsigned with 4294967295%Z; lia. }
    lia.
  - assert (Heq: z_of_breg r = i).
    + unfold z_of_breg.
      unfold Int.eq in HE.
      rewrite Int.unsigned_repr in HE.
      2:{ change Int.max_unsigned with 4294967295%Z; destruct r; lia. }
      rewrite Int.unsigned_repr in HE.
      2:{ change Int.max_unsigned with 4294967295%Z; lia. }
      eapply zeq_true in HE; try lia.
    + rewrite <- Heq.
      unfold z_of_breg.
      destruct r; lia.
Qed.

Lemma reg_lt_false_r:
  forall i r, (0 <= i < 16)%Z -> Int.ltu (int_of_breg r) (Int.repr i) = false -> ((z_of_breg r) >= i)%Z.
Proof.
  unfold int_of_breg, z_of_breg.
  intros i r Hc Hlt.
  rewrite <- Bool.negb_true_iff in Hlt.
  rewrite Int.not_ltu in Hlt.
  rewrite Bool.orb_true_iff in Hlt.
  destruct Hlt as [HL | HE].
  - eapply Int.ltu_inv in HL.
    rewrite Int.unsigned_repr in HL.
    2:{ change Int.max_unsigned with 4294967295%Z; lia. }
    rewrite Int.unsigned_repr in HL.
    2:{ change Int.max_unsigned with 4294967295%Z; destruct r; lia. }
    lia.
  - assert (Heq: z_of_breg r = i).
    + unfold z_of_breg.
      unfold Int.eq in HE.
      rewrite Int.unsigned_repr in HE.
      2:{ change Int.max_unsigned with 4294967295%Z; lia. }
      rewrite Int.unsigned_repr in HE.
      2:{ change Int.max_unsigned with 4294967295%Z; destruct r; lia. }
      eapply zeq_true in HE; try lia.
    + rewrite <- Heq.
      unfold z_of_breg.
      destruct r; lia.
Qed.

Lemma z_of_ireg_ge_0:
  forall r, (z_of_breg r >= 0)%Z.
Proof.
  intros.
  unfold z_of_breg.
  destruct r; lia.
Qed.

Ltac compute_Zmod :=
  match goal with
  | |- (?X | ?Y)%Z =>
    let v := (eval vm_compute in (Y/X)%Z) in
    try (replace Y with (v * X)%Z by reflexivity)
  end.

Ltac copy_to_solver :=
  let Heq := fresh "Heq" in
  let m0 := fresh "m0" in
  let Hstore0 := fresh "Hstore0" in
  match goal with
  | Hperm : Mem.range_perm ?m ?st_blk 0%Z 52%Z Cur Writable
    |- context [Mem.store Mint32 ?m' ?st_blk ?X (?rs (BR ?r))] =>
    assert (Heq: exists m0, Mem.store Mint32 m st_blk X (rs (BR r)) = Some m0 /\
      Mem.range_perm m0 st_blk 0%Z 52%Z Cur Writable);
    [ assert (Heq: Mem.valid_access m Mint32 st_blk X Writable);
      [
        unfold Mem.valid_access;
        unfold Mem.range_perm in *;
        split;
        [ intros ofs Hofs; apply Hperm; simpl in Hofs; lia |
          simpl; compute_Zmod; apply Z.divide_factor_r
        ] |
        eapply Mem.valid_access_store with (v := (rs (BR r))) in Heq; eauto;
        destruct Heq as (mk & Hstore);
        exists mk; split;
          [ simpl; auto |
            unfold Mem.range_perm in *; intros ofs Hofs; eapply Mem.perm_store_1; eauto
          ]
      ] |
      clear Hperm; destruct Heq as (m0 & Hstore0 & Hperm);
      rewrite Hstore0
    ]
  end.

Ltac load_store_same_solver :=
  match goal with
  | REG_INV : forall r : BPregEq.t, exists vi : int, ?rs r = Vint vi,
    Hstore11 : Mem.store Mint32 ?m10 ?st_blk ?X (?rs ?R) = Some ?m11
     |- Mem.load Mint32 ?m11 ?st_blk ?X = Some (?rs ?R) =>
    erewrite Mem.load_store_same; eauto;
    specialize (REG_INV R);
    destruct REG_INV as (v_r & Heq);
    rewrite Heq;
    unfold Val.load_result; f_equal
  end.

Lemma copy_to_prop:
  forall m m' rs st_blk jit_blk
    (HBLK_VALID : Mem.valid_block m jit_blk)
    (REG_INV: forall r, exists vi, rs#r = Vint vi)
    (Halloc : Mem.alloc m 0 state_block_size = (m', st_blk)),
    exists mk,
        copy_to rs st_blk m' = Some mk /\
        (Mem.valid_block mk jit_blk) /\
        (forall r, Mem.load Mint32 mk st_blk (z_of_breg r * 4) = Some (rs#r)) /\
        (Mem.load Mint32 mk st_blk 44%Z = Some (rs#BPC)) /\
        (Mem.range_perm mk st_blk 0%Z state_block_size Cur Writable).
Proof.
  unfold copy_to, state_block_size.
  intros.

  assert (Heq: Mem.range_perm m' st_blk 0%Z 52%Z Cur Writable). {
    unfold Mem.range_perm.
    intros ofs Hofs_range.
    eapply Mem.perm_alloc_2 with (k:= Cur) in Hofs_range; eauto.
    eapply Mem.perm_implies; eauto.
    constructor.
  }
  rename Heq into Hperm.

  repeat copy_to_solver.

  assert (Heq: exists m11, Mem.store Mint32 m10 st_blk 44 (rs BPC) = Some m11 /\
    Mem.range_perm m11 st_blk 0%Z 52%Z Cur Writable);
  [ assert (Heq: Mem.valid_access m10 Mint32 st_blk 44 Writable);
    [
      unfold Mem.valid_access;
      unfold Mem.range_perm in *;
      split;
      [ intros ofs Hofs; apply Hperm; simpl in Hofs; lia |
        simpl; compute_Zmod; apply Z.divide_factor_r
      ] |
      eapply Mem.valid_access_store with (v := (rs BPC)) in Heq; eauto;
      destruct Heq as (mk & Hstore);
      exists mk; split;
        [ simpl; auto |
          unfold Mem.range_perm in *; intros ofs Hofs; eapply Mem.perm_store_1; eauto
        ]
    ] |
    clear Hperm; destruct Heq as (m11 & Hstore11 & Hperm);
    rewrite Hstore11
  ].

  exists m11.
  split; [auto | ].

  split.
  {
    do 12 (eapply Mem.store_valid_block_1; eauto).
    eapply Mem.valid_block_alloc; eauto.
  }

  split.
  2:{
    split; auto.
    load_store_same_solver.
  }

  intros.
  destruct r; simpl;
    repeat (erewrite Mem.load_store_other; eauto; [| simpl; lia]);
    load_store_same_solver.
Qed.

Ltac copy_from_solver X :=
  let HR0 := fresh "HR0" in
  match goal with
  | Hsyn : forall r : breg, Mem.load Mint32 ?m ?st_blk (z_of_breg r * 4)%Z = Some (?rs (BR r)) |- _ =>
    specialize (Hsyn X) as HR0; simpl in HR0; rewrite HR0
  end.

Lemma copy_from_prop:
  forall m st_blk (rs0 rs: regset)
    (HPERM : Mem.range_perm m st_blk 0 state_block_size Cur Writable)
    (Hpc : Mem.load Mint32 m st_blk 44 = Some (rs BPC))
    (Hsyn : forall r : breg, Mem.load Mint32 m st_blk (z_of_breg r * 4) = Some (rs r)),
      copy_from rs0 st_blk m = Some rs.
Proof.
  unfold state_block_size, copy_from; intros.
  copy_from_solver R0.
  copy_from_solver R1.
  copy_from_solver R2.
  copy_from_solver R3.
  copy_from_solver R4.
  copy_from_solver R5.
  copy_from_solver R6.
  copy_from_solver R7.
  copy_from_solver R8.
  copy_from_solver R9.
  copy_from_solver R10.
  rewrite Hpc.
  f_equal.
  extensionality r.
  unfold BPregmap.set.
  unfold BPregEq.eq.
  repeat (destruct bpreg_eq; [subst r; auto|]).
  exfalso.
  destruct r eqn: Heq.
  - destruct b;
    match goal with
    | H: ?X <> ?X |- False => apply H; reflexivity
    end.
  - apply n; reflexivity.
Qed.