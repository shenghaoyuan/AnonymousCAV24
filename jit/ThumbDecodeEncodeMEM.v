From compcert.common Require Import Values Memory AST.
From compcert.lib Require Import Integers Maps.
From compcert.arm Require Import AsmSyntax BinSyntax BinDecode ABinSem.

From bpf.rbpf32 Require Import TSSyntax JITConfig.

From bpf.jit Require Import (*ThumbEncode *) Arm32Reg ThumbInsOp.
From bpf.jit Require Import BitfieldLemma ThumbJITLtac.

From Coq Require Import List ZArith Lia.
Open Scope nat_scope.
Open Scope bool_scope.
Import ListNotations.

Lemma is_thumb2_STR_LDR:
  forall x y z op,
    op = LDR_I_OP \/ op = STR_I_OP ->
      decode_arm32
       (encode_arm32 (encode_arm32 x y 12 4)
          (encode_arm32 z op 0 4) 16 16) 11 5 = Int.repr 31.
Proof.
  unfold STR_I_OP, LDR_I_OP, decode_arm32, encode_arm32.
  intros.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 11%Z) (width1 := 5%Z);
    change Int.zwordsize with 32%Z; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 11%Z) (width1 := 5%Z);
    change Int.zwordsize with 32%Z; try lia;
      [| reflexivity | reflexivity ].
  destruct H; subst op; auto.
Qed.

Lemma decode_arm32_STR_LDR_11_5:
  forall x y ir op,
    op = LDR_I_OP \/ op = STR_I_OP ->
      (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 x y 12 4)
             (encode_arm32 (int_of_ireg ir) op 0 4) 16 16) 0 16) 11 5) = Int.repr 31.
Proof.
  unfold STR_I_OP, LDR_I_OP, decode_arm32, encode_arm32.
  intros.
  remember (Int.unsigned_bitfield_extract (Z.of_nat 0) (Z.of_nat 16) _) as k eqn: Ht.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z) in Ht;
    change Int.zwordsize with 32%Z; try lia;
      [| reflexivity | reflexivity ].

  subst k. unfold int_of_ireg;
  destruct H; subst op; destruct ir; simpl; auto.
Qed.

Lemma decode_arm32_STR_LDR_9_2:
  forall x y ir op,
    op = LDR_I_OP \/ op = STR_I_OP ->
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 x y 12 4)
             (encode_arm32 (int_of_ireg ir) op 0 4) 16 16) 0 16) 9 2) = Int.zero.
Proof.
  unfold STR_I_OP, LDR_I_OP, decode_arm32, encode_arm32.
  intros.
  remember (Int.unsigned_bitfield_extract (Z.of_nat 0) (Z.of_nat 16) _) as k eqn: Ht.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z) in Ht;
    change Int.zwordsize with 32%Z; try lia;
      [| reflexivity | reflexivity ].

  subst k. unfold int_of_ireg;
  destruct H; subst op; destruct ir; simpl; auto.
Qed.

Lemma decode_arm32_STR_LDR_5_4:
  forall x y ir op,
    op = LDR_I_OP \/ op = STR_I_OP ->
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 x y 12 4)
             (encode_arm32 (int_of_ireg ir) op 0 4) 16 16) 0 16) 5 4) = Int.repr 6.
Proof.
  unfold STR_I_OP, LDR_I_OP, decode_arm32, encode_arm32.
  intros.
  remember (Int.unsigned_bitfield_extract (Z.of_nat 0) (Z.of_nat 16) _) as k eqn: Ht.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z) in Ht;
    change Int.zwordsize with 32%Z; try lia;
      [| reflexivity | reflexivity ].

  subst k. unfold int_of_ireg;
  destruct H; subst op; destruct ir; simpl; auto.
Qed.

Lemma decode_arm32_OP_0_12:
  forall br ir op,
    (decode_arm32
          (decode_arm32
             (encode_arm32
                (encode_arm32 (int_of_breg br) (Int.mul (int_of_breg br) (Int.repr 4)) 12 4)
                (encode_arm32 (int_of_ireg ir) op 0 4) 16 16) 16 16) 0 12) = (Int.mul (int_of_breg br) (Int.repr 4)).
Proof.
  intros.
  unfold decode_arm32, encode_arm32.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    change Int.zwordsize with 32%Z; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia;
      unfold int_of_breg; destruct br; prove_int.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 12%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 12%Z);
    change Int.zwordsize with 32%Z; try lia;
      [| reflexivity | reflexivity ].
  rewrite unsigned_bitfield_extract_low_same; auto.
  - change Int.zwordsize with 32%Z; lia.
  - destruct br; unfold int_of_breg; simpl; prove_int.
Qed.

Lemma decode_arm32_STR_LDR_0_4:
  forall x y ir op,
    op = LDR_I_OP \/ op = STR_I_OP ->
    (decode_arm32
         (decode_arm32
            (encode_arm32
               (encode_arm32 x y 12 4)
               (encode_arm32 (int_of_ireg ir) op 0 4) 16 16) 0 16) 0 4) = (int_of_ireg ir).
Proof.
  unfold STR_I_OP, LDR_I_OP, decode_arm32, encode_arm32.
  intros.
  remember (Int.unsigned_bitfield_extract (Z.of_nat 0) (Z.of_nat 16) _) as k eqn: Ht.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z) in Ht;
    change Int.zwordsize with 32%Z; try lia;
      [| reflexivity | reflexivity ].

  subst k. unfold int_of_ireg;
  destruct H; subst op; destruct ir; simpl; auto.
Qed.

Lemma decode_arm32_breg_12_4:
  forall br ir op,
  (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (int_of_breg br) (Int.mul (int_of_breg br) (Int.repr 4)) 12 4)
             (encode_arm32 (int_of_ireg ir) op 0 4) 16 16) 16 16) 12 4) = (int_of_breg br).
Proof.
  intros.
  unfold decode_arm32, encode_arm32.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    change Int.zwordsize with 32%Z; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia;
      unfold int_of_breg; destruct br; prove_int.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same with
    (pos := 12%Z) (width := 4%Z);
    change Int.zwordsize with 32%Z; try lia; eauto.
  instantiate (1 := Int.bitfield_insert 12 4 Int.zero (int_of_breg br)).
  destruct br; repeat int_true_false.
Qed.

Lemma decode_arm32_STR_I_OP_4_1:
  forall br ir,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (int_of_breg br) (Int.mul (int_of_breg br) (Int.repr 4)) 12 4)
             (encode_arm32 (int_of_ireg ir) STR_I_OP 0 4) 16 16) 0 16) 4 1) = Int.zero.
Proof.
  intros.
  unfold STR_I_OP, decode_arm32, encode_arm32.
  remember (Int.unsigned_bitfield_extract (Z.of_nat 0) (Z.of_nat 16) _) as k eqn: Ht.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z) in Ht;
    change Int.zwordsize with 32%Z; try lia;
      [| reflexivity | reflexivity ].

  subst k. unfold int_of_ireg; destruct ir; simpl; auto.
Qed.

Lemma decode_arm32_LDR_I_OP_4_1:
  forall br ir,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg br) (Int.mul (int_of_breg br) (Int.repr 4)) 12 4)
             (encode_arm32 (int_of_ireg ir) LDR_I_OP 0 4) 16 16) 0 16) 4 1) = Int.one.
Proof.
  intros.
  unfold LDR_I_OP, decode_arm32, encode_arm32.
  remember (Int.unsigned_bitfield_extract (Z.of_nat 0) (Z.of_nat 16) _) as k eqn: Ht.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z) in Ht;
    change Int.zwordsize with 32%Z; try lia;
      [| reflexivity | reflexivity ].

  subst k; destruct ir; simpl; auto.
Qed.

Lemma decode_str_i_13:
  forall br,
      decode_thumb
      (encode_arm32
         (encode_arm32 (int_of_breg br) (Int.mul (int_of_breg br) (Int.repr 4)) 12 4)
         (encode_arm32 (int_of_ireg IR13) STR_I_OP 0 4) 16 16) =
        Some (Pstr_a (ireg_of_breg br) IR13
                (SOimm (Int.mul (int_of_breg br) (Int.repr 4)))).
Proof.
  intros.
  unfold decode_thumb.

  rewrite is_thumb2_STR_LDR with (op := STR_I_OP); [| right; reflexivity].
  (**r using `replace` instead of `change`, because Coq checker will no response for `change` *)
  replace (Int.eq (Int.repr 31) (Int.repr 23)) with false by reflexivity; simpl.

  unfold decode_thumb2.
  rewrite decode_arm32_STR_LDR_11_5 with (op := STR_I_OP); [| right; reflexivity].
  replace (Int.eq (Int.repr 31) (Int.repr 29)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 30)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 31)) with true by reflexivity; simpl.

  rewrite decode_arm32_STR_LDR_9_2 with (op := STR_I_OP); [| right; reflexivity].
  rewrite Int.eq_true.
  rewrite decode_arm32_STR_LDR_5_4 with (op := STR_I_OP); [| right; reflexivity].
  replace (Int.eq (Int.repr 6) (Int.repr 2)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 6) (Int.repr 6)) with true by reflexivity; simpl.

  rewrite decode_arm32_OP_0_12.
  rewrite int_ltu_0, int_ltu_4095_mul_breg_4.
  simpl.

  rewrite decode_arm32_STR_LDR_0_4 with (op := STR_I_OP); [| right; reflexivity].
  rewrite int2ireg_int_of_ireg_same.

  rewrite decode_arm32_breg_12_4.
  rewrite int2ireg_int_of_breg_same.

  rewrite decode_arm32_STR_I_OP_4_1.
  rewrite Int.eq_true.
  unfold BinDecode.ireg_eqb; simpl.
  f_equal.
Qed.

Lemma decode_ldr_i_12:
  forall br,
    decode_thumb
      (encode_arm32 (encode_arm32 (int_of_breg br) (Int.mul (int_of_breg br) (Int.repr 4)) 12 4)
         (encode_arm32 (int_of_ireg IR12) LDR_I_OP 0 4) 16 16) =
        Some (Pldr (ireg_of_breg br) IR12
                (SOimm (Int.mul (int_of_breg br) (Int.repr 4)))).
Proof.
  intros.
  unfold decode_thumb.

  rewrite is_thumb2_STR_LDR with (op := LDR_I_OP); [| left; reflexivity].
  replace (Int.eq (Int.repr 31) (Int.repr 23)) with false by reflexivity; simpl.

  unfold decode_thumb2.
  rewrite decode_arm32_STR_LDR_11_5 with (op := LDR_I_OP); [| left; reflexivity].
  replace (Int.eq (Int.repr 31) (Int.repr 29)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 30)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 31)) with true by reflexivity; simpl.

  rewrite decode_arm32_STR_LDR_9_2 with (op := LDR_I_OP); [| left; reflexivity].
  rewrite Int.eq_true.
  rewrite decode_arm32_STR_LDR_5_4 with (op := LDR_I_OP); [| left; reflexivity].
  replace (Int.eq (Int.repr 6) (Int.repr 2)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 6) (Int.repr 6)) with true by reflexivity; simpl.

  rewrite decode_arm32_OP_0_12.
  rewrite int_ltu_0, int_ltu_4095_mul_breg_4.
  simpl.

  rewrite decode_arm32_STR_LDR_0_4 with (op := LDR_I_OP); [| left; reflexivity].
  rewrite int2ireg_int_of_ireg_same.

  rewrite decode_arm32_breg_12_4.
  rewrite int2ireg_int_of_breg_same.

  rewrite decode_arm32_LDR_I_OP_4_1.
  replace (Int.eq Int.one Int.zero) with false by reflexivity.
  rewrite Int.eq_true.
  simpl. 
  f_equal.
Qed.

Lemma decode_ldr_i_12_11:
  decode_thumb
    (encode_arm32 (encode_arm32 (Int.repr 11) (Int.repr 44) 12 4)
        (encode_arm32 (int_of_ireg IR12) LDR_I_OP 0 4) 16 16) =
        Some (Pldr IR11 IR12 (SOimm (Int.repr 44))).
Proof.
  unfold decode_thumb.
  rewrite is_thumb2_STR_LDR with (op := LDR_I_OP); [| left; reflexivity].
  replace (Int.eq (Int.repr 31) (Int.repr 23)) with false by reflexivity; simpl.

  unfold decode_thumb2.
  rewrite decode_arm32_STR_LDR_11_5 with (op := LDR_I_OP); [| left; reflexivity].
  replace (Int.eq (Int.repr 31) (Int.repr 29)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 30)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 31)) with true by reflexivity; simpl.

  rewrite decode_arm32_STR_LDR_9_2 with (op := LDR_I_OP); [| left; reflexivity].
  rewrite Int.eq_true.
  rewrite decode_arm32_STR_LDR_5_4 with (op := LDR_I_OP); [| left; reflexivity].
  replace (Int.eq (Int.repr 6) (Int.repr 2)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 6) (Int.repr 6)) with true by reflexivity; simpl.

  assert (Heq:
    (decode_arm32
          (decode_arm32
             (encode_arm32 (encode_arm32 (Int.repr 11) (Int.repr 44) 12 4)
                (encode_arm32 (int_of_ireg IR12) LDR_I_OP 0 4) 16 16) 16 16) 0 12) =
    (Int.repr 44)). {
    unfold decode_arm32, encode_arm32.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      change Int.zwordsize with 32%Z; try lia; eauto.
    prove_int.
  }
  rewrite Heq; clear Heq.

  rewrite int_ltu_0. change (Int.ltu (Int.repr 4095) (Int.repr 44)) with false.
  simpl.

  rewrite decode_arm32_STR_LDR_0_4 with (op := LDR_I_OP); [| left; reflexivity].
  rewrite int2ireg_int_of_ireg_same.

  assert (Heq:
  (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 11) (Int.repr 44) 12 4)
             (encode_arm32 (int_of_ireg IR12) LDR_I_OP 0 4) 16 16) 16 16) 12 4) = (Int.repr 11)). {
    unfold decode_arm32, encode_arm32.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      change Int.zwordsize with 32%Z; try lia; eauto.
    prove_int.
  }
  rewrite Heq; clear Heq.

  assert (Heq: int2ireg (Int.repr 11) = Some IR11). {
    unfold int2ireg.
    simpl; auto.
  }
  rewrite Heq; clear Heq.

  assert (Heq:
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 11) (Int.repr 44) 12 4)
             (encode_arm32 (int_of_ireg IR12) LDR_I_OP 0 4) 16 16) 0 16) 4 1) = Int.one). {
    unfold LDR_I_OP, decode_arm32, encode_arm32.
    remember (Int.unsigned_bitfield_extract (Z.of_nat 0) (Z.of_nat 16) _) as k eqn: Ht.
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z) in Ht;
      change Int.zwordsize with 32%Z; try lia;
        [| reflexivity | reflexivity ].

    subst k; simpl; auto.
  }
  rewrite Heq; clear Heq.

  replace (Int.eq Int.one Int.zero) with false by reflexivity.
  rewrite Int.eq_true.
  simpl. 
  f_equal.
Qed.

Lemma decode_ldr_i_13:
  forall br,
    decode_thumb
      (encode_arm32 (encode_arm32 (int_of_breg br) (Int.mul (int_of_breg br) (Int.repr 4)) 12 4)
         (encode_arm32 (int_of_ireg IR13) LDR_I_OP 0 4) 16 16) =
        Some (Pldr_a (ireg_of_breg br) IR13
                (SOimm (Int.mul (int_of_breg br) (Int.repr 4)))).
Proof.
  intros.
  unfold decode_thumb.

  rewrite is_thumb2_STR_LDR with (op := LDR_I_OP); [| left; reflexivity].
  replace (Int.eq (Int.repr 31) (Int.repr 23)) with false by reflexivity; simpl.

  unfold decode_thumb2.
  rewrite decode_arm32_STR_LDR_11_5 with (op := LDR_I_OP); [| left; reflexivity].
  replace (Int.eq (Int.repr 31) (Int.repr 29)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 30)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 31)) with true by reflexivity; simpl.

  rewrite decode_arm32_STR_LDR_9_2 with (op := LDR_I_OP); [| left; reflexivity].
  rewrite Int.eq_true.
  rewrite decode_arm32_STR_LDR_5_4 with (op := LDR_I_OP); [| left; reflexivity].
  replace (Int.eq (Int.repr 6) (Int.repr 2)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 6) (Int.repr 6)) with true by reflexivity; simpl.

  rewrite decode_arm32_OP_0_12.
  rewrite int_ltu_0, int_ltu_4095_mul_breg_4.
  simpl.

  rewrite decode_arm32_STR_LDR_0_4 with (op := LDR_I_OP); [| left; reflexivity].
  rewrite int2ireg_int_of_ireg_same.

  rewrite decode_arm32_breg_12_4.
  rewrite int2ireg_int_of_breg_same.

  rewrite decode_arm32_LDR_I_OP_4_1.
  replace (Int.eq Int.one Int.zero) with false by reflexivity.
  rewrite Int.eq_true.
  simpl.
  f_equal.
Qed.

Lemma decode_ldr_i_13_11:
  decode_thumb
    (encode_arm32 (encode_arm32 (Int.repr 11) (Int.repr 44) 12 4)
        (encode_arm32 (int_of_ireg IR13) LDR_I_OP 0 4) 16 16) =
        Some (Pldr_a IR11 IR13 (SOimm (Int.repr 44))).
Proof.
  unfold decode_thumb.
  rewrite is_thumb2_STR_LDR with (op := LDR_I_OP); [| left; reflexivity].
  replace (Int.eq (Int.repr 31) (Int.repr 23)) with false by reflexivity; simpl.

  unfold decode_thumb2.
  rewrite decode_arm32_STR_LDR_11_5 with (op := LDR_I_OP); [| left; reflexivity].
  replace (Int.eq (Int.repr 31) (Int.repr 29)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 30)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 31)) with true by reflexivity; simpl.

  rewrite decode_arm32_STR_LDR_9_2 with (op := LDR_I_OP); [| left; reflexivity].
  rewrite Int.eq_true.
  rewrite decode_arm32_STR_LDR_5_4 with (op := LDR_I_OP); [| left; reflexivity].
  replace (Int.eq (Int.repr 6) (Int.repr 2)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 6) (Int.repr 6)) with true by reflexivity; simpl.

  assert (Heq:
    (decode_arm32
          (decode_arm32
             (encode_arm32 (encode_arm32 (Int.repr 11) (Int.repr 44) 12 4)
                (encode_arm32 (int_of_ireg IR13) LDR_I_OP 0 4) 16 16) 16 16) 0 12) =
    (Int.repr 44)). {
    unfold decode_arm32, encode_arm32.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      change Int.zwordsize with 32%Z; try lia; eauto.
    prove_int.
  }
  rewrite Heq; clear Heq.

  rewrite int_ltu_0. change (Int.ltu (Int.repr 4095) (Int.repr 44)) with false.
  simpl.

  rewrite decode_arm32_STR_LDR_0_4 with (op := LDR_I_OP); [| left; reflexivity].
  rewrite int2ireg_int_of_ireg_same.

  assert (Heq:
  (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 11) (Int.repr 44) 12 4)
             (encode_arm32 (int_of_ireg IR13) LDR_I_OP 0 4) 16 16) 16 16) 12 4) = (Int.repr 11)). {
    unfold decode_arm32, encode_arm32.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      change Int.zwordsize with 32%Z; try lia; eauto.
    prove_int.
  }
  rewrite Heq; clear Heq.

  assert (Heq: int2ireg (Int.repr 11) = Some IR11). {
    unfold int2ireg.
    simpl; auto.
  }
  rewrite Heq; clear Heq.

  assert (Heq:
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 11) (Int.repr 44) 12 4)
             (encode_arm32 (int_of_ireg IR13) LDR_I_OP 0 4) 16 16) 0 16) 4 1) = Int.one). {
    unfold LDR_I_OP, decode_arm32, encode_arm32.
    remember (Int.unsigned_bitfield_extract (Z.of_nat 0) (Z.of_nat 16) _) as k eqn: Ht.
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z) in Ht;
      change Int.zwordsize with 32%Z; try lia;
        [| reflexivity | reflexivity ].

    subst k; simpl; auto.
  }
  rewrite Heq; clear Heq.

  replace (Int.eq Int.one Int.zero) with false by reflexivity.
  rewrite Int.eq_true.
  simpl.
  f_equal.
Qed.

Lemma decode_ldr_i_13_13:
  decode_thumb
      (encode_arm32 (encode_arm32 (int_of_ireg IR13) Int.zero 12 4)
         (encode_arm32 (int_of_ireg IR13) LDR_I_OP 0 4) 16 16) =
        Some (Pldr_a IR13 IR13 (SOimm Int.zero)).
Proof.
  unfold decode_thumb.
  rewrite is_thumb2_STR_LDR with (op := LDR_I_OP); [| left; reflexivity].
  replace (Int.eq (Int.repr 31) (Int.repr 23)) with false by reflexivity; simpl.

  unfold decode_thumb2.
  rewrite decode_arm32_STR_LDR_11_5 with (op := LDR_I_OP); [| left; reflexivity].
  replace (Int.eq (Int.repr 31) (Int.repr 29)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 30)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 31)) with true by reflexivity; simpl.

  rewrite decode_arm32_STR_LDR_9_2 with (op := LDR_I_OP); [| left; reflexivity].
  rewrite Int.eq_true.
  rewrite decode_arm32_STR_LDR_5_4 with (op := LDR_I_OP); [| left; reflexivity].
  replace (Int.eq (Int.repr 6) (Int.repr 2)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 6) (Int.repr 6)) with true by reflexivity; simpl.

  assert (Heq:
    (decode_arm32
          (decode_arm32
             (encode_arm32 (encode_arm32 (int_of_ireg IR13) Int.zero 12 4)
                (encode_arm32 (int_of_ireg IR13) LDR_I_OP 0 4) 16 16) 16 16) 0 12) =
    Int.zero). {
    unfold decode_arm32, encode_arm32, Int.zero.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      change Int.zwordsize with 32%Z; try lia; eauto.
    prove_int.
  }
  rewrite Heq; clear Heq.

  rewrite int_ltu_0. change (Int.ltu (Int.repr 4095) Int.zero) with false.
  simpl.

  rewrite decode_arm32_STR_LDR_0_4 with (op := LDR_I_OP); [| left; reflexivity].
  rewrite int2ireg_int_of_ireg_same.

  assert (Heq:
  decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_ireg IR13) Int.zero 12 4)
             (encode_arm32 (int_of_ireg IR13) LDR_I_OP 0 4) 16 16) 16 16) 12 4 = (Int.repr 13)). {
    unfold decode_arm32, encode_arm32.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      change Int.zwordsize with 32%Z; try lia; eauto.
    prove_int.
  }
  rewrite Heq; clear Heq.

  assert (Heq: int2ireg (Int.repr 13) = Some IR13). {
    unfold int2ireg.
    simpl; auto.
  }
  rewrite Heq; clear Heq.

  assert (Heq:
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_ireg IR13) Int.zero 12 4)
             (encode_arm32 (int_of_ireg IR13) LDR_I_OP 0 4) 16 16) 0 16) 4 1) = Int.one). {
    unfold LDR_I_OP, decode_arm32, encode_arm32.
    remember (Int.unsigned_bitfield_extract (Z.of_nat 0) (Z.of_nat 16) _) as k eqn: Ht.
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z) in Ht;
      change Int.zwordsize with 32%Z; try lia;
        [| reflexivity | reflexivity ].

    subst k; simpl; auto.
  }
  rewrite Heq; clear Heq.

  replace (Int.eq Int.one Int.zero) with false by reflexivity.
  rewrite Int.eq_true.
  simpl.
  f_equal.
Qed.

Lemma decode_str_i_12_11:
  decode_thumb
    (encode_arm32 (encode_arm32 (Int.repr 11) (Int.repr 44) 12 4)
      (encode_arm32 (int_of_ireg IR12) STR_I_OP 0 4) 16 16) =
      Some (Pstr IR11 IR12 (SOimm (Int.repr 44))).
Proof.
  intros.
  unfold decode_thumb.

  rewrite is_thumb2_STR_LDR with (op := STR_I_OP); [| right; reflexivity].
  (**r using `replace` instead of `change`, because Coq checker will no response for `change` *)
  replace (Int.eq (Int.repr 31) (Int.repr 23)) with false by reflexivity; simpl.

  unfold decode_thumb2.
  rewrite decode_arm32_STR_LDR_11_5 with (op := STR_I_OP); [| right; reflexivity].
  replace (Int.eq (Int.repr 31) (Int.repr 29)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 30)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 31)) with true by reflexivity; simpl.

  rewrite decode_arm32_STR_LDR_9_2 with (op := STR_I_OP); [| right; reflexivity].
  rewrite Int.eq_true.
  rewrite decode_arm32_STR_LDR_5_4 with (op := STR_I_OP); [| right; reflexivity].
  replace (Int.eq (Int.repr 6) (Int.repr 2)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 6) (Int.repr 6)) with true by reflexivity; simpl.

  assert (Heq:
    (decode_arm32
      (decode_arm32
         (encode_arm32 (encode_arm32 (Int.repr 11) (Int.repr 44) 12 4)
            (encode_arm32 (int_of_ireg IR12) STR_I_OP 0 4) 16 16) 16 16) 0 12) = (Int.repr 44)). {
    unfold decode_arm32, encode_arm32.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      change Int.zwordsize with 32%Z; try lia; eauto.
    prove_int.
  }
  rewrite Heq; clear Heq.

  rewrite int_ltu_0. replace (Int.ltu (Int.repr 4095) (Int.repr 44)) with false by reflexivity.
  simpl.

  rewrite decode_arm32_STR_LDR_0_4 with (op := STR_I_OP); [| right; reflexivity].
  rewrite int2ireg_int_of_ireg_same.

  assert (Heq: (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 11) (Int.repr 44) 12 4)
             (encode_arm32 (int_of_ireg IR12) STR_I_OP 0 4) 16 16) 16 16) 12 4) = (Int.repr 11)). {
    unfold decode_arm32, encode_arm32.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      change Int.zwordsize with 32%Z; try lia; eauto.
    prove_int.
  }
  rewrite Heq; clear Heq.

  assert (Heq: int2ireg (Int.repr 11) = Some IR11). {
    unfold int2ireg.
    simpl; auto.
  }
  rewrite Heq; clear Heq.

  assert (Heq:
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 11) (Int.repr 44) 12 4)
             (encode_arm32 (int_of_ireg IR12) STR_I_OP 0 4) 16 16) 0 16) 4 1) = Int.zero). {
    unfold STR_I_OP, decode_arm32, encode_arm32.
    remember (Int.unsigned_bitfield_extract (Z.of_nat 0) (Z.of_nat 16) _) as k eqn: Ht.
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z) in Ht;
      change Int.zwordsize with 32%Z; try lia;
        [| reflexivity | reflexivity ].

    subst k. unfold int_of_ireg; simpl; auto.
  }

  rewrite Int.eq_true.
  unfold BinDecode.ireg_eqb; simpl.
  f_equal.
Qed.

Lemma decode_str_i_13_11:
  decode_thumb
      (encode_arm32 (encode_arm32 (Int.repr 11) (Int.repr 44) 12 4)
         (encode_arm32 (int_of_ireg IR13) STR_I_OP 0 4) 16 16) =
      Some (Pstr_a IR11 IR13 (SOimm (Int.repr 44))).
Proof.
  intros.
  unfold decode_thumb.

  rewrite is_thumb2_STR_LDR with (op := STR_I_OP); [| right; reflexivity].
  (**r using `replace` instead of `change`, because Coq checker will no response for `change` *)
  replace (Int.eq (Int.repr 31) (Int.repr 23)) with false by reflexivity; simpl.

  unfold decode_thumb2.
  rewrite decode_arm32_STR_LDR_11_5 with (op := STR_I_OP); [| right; reflexivity].
  replace (Int.eq (Int.repr 31) (Int.repr 29)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 30)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 31)) with true by reflexivity; simpl.

  rewrite decode_arm32_STR_LDR_9_2 with (op := STR_I_OP); [| right; reflexivity].
  rewrite Int.eq_true.
  rewrite decode_arm32_STR_LDR_5_4 with (op := STR_I_OP); [| right; reflexivity].
  replace (Int.eq (Int.repr 6) (Int.repr 2)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 6) (Int.repr 6)) with true by reflexivity; simpl.

  assert (Heq:
    (decode_arm32
          (decode_arm32
             (encode_arm32 (encode_arm32 (Int.repr 11) (Int.repr 44) 12 4)
                (encode_arm32 (int_of_ireg IR13) STR_I_OP 0 4) 16 16) 16 16) 0 12) = (Int.repr 44)). {
    unfold decode_arm32, encode_arm32.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      change Int.zwordsize with 32%Z; try lia; eauto.
    prove_int.
  }
  rewrite Heq; clear Heq.

  rewrite int_ltu_0. replace (Int.ltu (Int.repr 4095) (Int.repr 44)) with false by reflexivity.
  simpl.

  rewrite decode_arm32_STR_LDR_0_4 with (op := STR_I_OP); [| right; reflexivity].
  rewrite int2ireg_int_of_ireg_same.

  assert (Heq: (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 11) (Int.repr 44) 12 4)
             (encode_arm32 (int_of_ireg IR13) STR_I_OP 0 4) 16 16) 16 16) 12 4) = (Int.repr 11)). {
    unfold decode_arm32, encode_arm32.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      change Int.zwordsize with 32%Z; try lia; eauto.
    prove_int.
  }
  rewrite Heq; clear Heq.

  assert (Heq: int2ireg (Int.repr 11) = Some IR11). {
    unfold int2ireg.
    simpl; auto.
  }
  rewrite Heq; clear Heq.

  assert (Heq:
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 11) (Int.repr 44) 12 4)
             (encode_arm32 (int_of_ireg IR13) STR_I_OP 0 4) 16 16) 0 16) 4 1) = Int.zero). {
    unfold STR_I_OP, decode_arm32, encode_arm32.
    remember (Int.unsigned_bitfield_extract (Z.of_nat 0) (Z.of_nat 16) _) as k eqn: Ht.
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z) in Ht;
      change Int.zwordsize with 32%Z; try lia;
        [| reflexivity | reflexivity ].

    subst k. unfold int_of_ireg; simpl; auto.
  }

  rewrite Int.eq_true.
  unfold BinDecode.ireg_eqb; simpl.
  f_equal.
Qed.

Lemma decode_str_i_12:
  forall br,
  decode_thumb
      (encode_arm32 (encode_arm32 (int_of_breg br) (Int.mul (int_of_breg br) (Int.repr 4)) 12 4)
         (encode_arm32 (int_of_ireg IR12) STR_I_OP 0 4) 16 16) =
        Some (Pstr (ireg_of_breg br) IR12
                (SOimm (Int.mul (int_of_breg br) (Int.repr 4)))).
Proof.
  intros.
  unfold decode_thumb.

  rewrite is_thumb2_STR_LDR with (op := STR_I_OP); [| right; reflexivity].
  (**r using `replace` instead of `change`, because Coq checker will no response for `change` *)
  replace (Int.eq (Int.repr 31) (Int.repr 23)) with false by reflexivity; simpl.

  unfold decode_thumb2.
  rewrite decode_arm32_STR_LDR_11_5 with (op := STR_I_OP); [| right; reflexivity].
  replace (Int.eq (Int.repr 31) (Int.repr 29)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 30)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 31)) with true by reflexivity; simpl.

  rewrite decode_arm32_STR_LDR_9_2 with (op := STR_I_OP); [| right; reflexivity].
  rewrite Int.eq_true.
  rewrite decode_arm32_STR_LDR_5_4 with (op := STR_I_OP); [| right; reflexivity].
  replace (Int.eq (Int.repr 6) (Int.repr 2)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 6) (Int.repr 6)) with true by reflexivity; simpl.
  rewrite decode_arm32_OP_0_12.

  rewrite int_ltu_0, int_ltu_4095_mul_breg_4.
  simpl.

  rewrite decode_arm32_STR_LDR_0_4 with (op := STR_I_OP); [| right; reflexivity].
  rewrite int2ireg_int_of_ireg_same.

  rewrite decode_arm32_breg_12_4.
  rewrite int2ireg_int_of_breg_same.

  assert (Heq:
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg br) (Int.mul (int_of_breg br) (Int.repr 4)) 12 4)
             (encode_arm32 (int_of_ireg IR12) STR_I_OP 0 4) 16 16) 0 16) 4 1) = Int.zero). {
    unfold STR_I_OP, decode_arm32, encode_arm32.
    remember (Int.unsigned_bitfield_extract (Z.of_nat 0) (Z.of_nat 16) _) as k eqn: Ht.
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z) in Ht;
      change Int.zwordsize with 32%Z; try lia;
        [| reflexivity | reflexivity ].

    subst k. unfold int_of_ireg; simpl; auto.
  }
  rewrite Heq; clear Heq.
  rewrite Int.eq_true.
  simpl. 
  f_equal.
Qed.