From compcert.common Require Import Values Memory AST.
From compcert.lib Require Import Integers Maps Zbits.
From compcert.arm Require Import AsmSyntax BinSyntax BinDecode ABinSem.

From bpf.comm Require Import LemmaInt.
From bpf.rbpf32 Require Import TSSyntax JITConfig.

From bpf.jit Require Import Arm32Reg ThumbInsOp ThumbJIT.
From bpf.jit Require Import BitfieldLemma ThumbJITLtac.

From Coq Require Import List ZArith Lia.
Open Scope nat_scope.
Open Scope bool_scope.
Import ListNotations.

Lemma int_le_0_255_size_8:
  forall si,
  Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
  (Int.size si <= 8)%Z.
Proof.
  intros.
  unfold Int.cmpu in *.
  replace 8%Z with (Int.size (Int.repr 255%Z)) by reflexivity.
  unfold Int.size.
  apply Zbits.Zsize_monotone.
  rewrite Bool.andb_true_iff in H.
  destruct H as (Hlo & Hhi).
  apply Cle_Zle_unsigned in Hlo, Hhi.
  replace (Int.unsigned (Int.repr 255)) with 255%Z in * by auto.
  replace (Int.unsigned Int.zero) with 0%Z in Hlo by auto.
  lia.
Qed.


Lemma int_le_0_32_size_5:
  forall si,
  Int.cmpu Cle Int.zero si && Int.cmpu Clt si (Int.repr 32) = true ->
    decode_arm32 si 0 16 = si.
Proof.
  unfold decode_arm32.
  intros.
  unfold Int.cmpu in *.
  assert (Heq: (Int.size si <= 5)%Z).
  - replace 5%Z with (Int.size (Int.repr 31%Z)) by reflexivity.
    unfold Int.size.
    apply Zbits.Zsize_monotone.
    rewrite Bool.andb_true_iff in H.
    destruct H as (Hlo & Hhi).
    apply Cle_Zle_unsigned in Hlo.
    apply Clt_Zlt_unsigned in Hhi.
    replace (Int.unsigned (Int.repr 32)) with 32%Z in * by auto.
    replace (Int.unsigned (Int.repr 31)) with 31%Z in * by auto.
    replace (Int.unsigned Int.zero) with 0%Z in Hlo by auto.
    lia.
  - apply unsigned_bitfield_extract_low_same;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
Qed.

Lemma decode_arm32_ADD_I_OP_LO_11_5:
  forall dst si,
    (decode_arm32
         (encode_arm32 (encode_arm32 dst si 8 4)
            (encode_arm32 dst ADD_I_OP 0 4) 16 16) 11 5) = Int.repr 30.
Proof.
  intros.
  unfold ADD_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  auto.
Qed.

Lemma decode_arm32_ADD_I_OP_HI_11_5:
  forall dst si,
  (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) ADD_I_OP 0 4) 16 16) 0 16) 11 5) = Int.repr 30.
Proof.
  intros.
  unfold ADD_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_ADD_I_OP_15_1:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    (decode_arm32
         (decode_arm32
            (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
               (encode_arm32 (int_of_breg dst) ADD_I_OP 0 4) 16 16) 16 16) 15 1) =
        Int.zero.
Proof.
  intros.
  unfold ADD_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 15%Z) (width1 := 1%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  eapply unsigned_bitfield_extract_over_size; eauto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
Qed.

Lemma decode_arm32_ADD_I_OP_5_4:
  forall dst si,
   (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) ADD_I_OP 0 4) 16 16) 0 16) 5 4) = (Int.repr 8).
Proof.
  intros.
  unfold ADD_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_ADD_I_OP_dst:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) ADD_I_OP 0 4) 16 16) 16 16) 8 4) =
        Some (ireg_of_breg dst).
Proof.
  intros.
  unfold ADD_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 8%Z) (width := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{ unfold int_of_breg; destruct dst; prove_int. }

  apply int2ireg_int_of_breg_same; auto.
Qed.

Lemma decode_arm32_ADD_I_OP_9_1:
  forall dst si,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) ADD_I_OP 0 4) 16 16) 0 16) 9 1) =
        Int.zero.
Proof.
  intros.
  unfold ADD_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_ADD_I_OP_4_1:
  forall dst si,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) ADD_I_OP 0 4) 16 16) 0 16) 4 1) =
        Int.zero.
Proof.
  intros.
  unfold ADD_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_ADD_I_OP_10_1:
  forall dst si,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) ADD_I_OP 0 4) 16
             16) 0 16) 10 1) =
        Int.zero.
Proof.
  intros.
  unfold ADD_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_ADD_I_OP_12_3:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) ADD_I_OP 0 4) 16
             16) 16 16) 12 3) =
        Int.zero.
Proof.
  intros.
  unfold ADD_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 12%Z) (width1 := 3%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  eapply unsigned_bitfield_extract_over_size; eauto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
Qed.

Lemma decode_arm32_ADD_I_OP_0_8:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) ADD_I_OP 0 4) 16
             16) 16 16) 0 8) = si.
Proof.
  intros.
  unfold ADD_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 8%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  apply unsigned_bitfield_extract_low_same; auto.
  replace Int.zwordsize with 32%Z by reflexivity; lia.
Qed.

Lemma decode_arm32_ADD_I_OP_dst2:
  forall dst si,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) ADD_I_OP 0 4) 16
             16) 0 16) 0 4) = Some (ireg_of_breg dst).
Proof.
  intros.
  unfold ADD_I_OP, NOP_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_add_i:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    decode_thumb
      (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
         (encode_arm32 (int_of_breg dst) ADD_I_OP 0 4) 16 16) =
      Some (Padd (ireg_of_breg dst) (ireg_of_breg dst) (SOimm si)).
Proof.
  intros dst si Hcmp.
  unfold decode_thumb.
  rewrite decode_arm32_ADD_I_OP_LO_11_5.
  replace (Int.eq (Int.repr 30) (Int.repr 23)) with false by reflexivity.
  unfold decode_thumb2.
  rewrite decode_arm32_ADD_I_OP_HI_11_5.
  replace (Int.eq (Int.repr 30) (Int.repr 29)) with false by reflexivity.
  rewrite Int.eq_true.
  rewrite decode_arm32_ADD_I_OP_15_1; [| assumption].
  rewrite Int.eq_true.
  rewrite decode_arm32_ADD_I_OP_5_4.
  replace (Int.eq (Int.repr 8) (Int.repr 13)) with false by reflexivity.
  rewrite Bool.andb_false_l.

  rewrite decode_arm32_ADD_I_OP_dst; [| assumption].
  rewrite decode_arm32_ADD_I_OP_9_1.
  replace (Int.eq Int.zero Int.one) with false by reflexivity.
  rewrite Bool.andb_false_l.
  rewrite decode_arm32_ADD_I_OP_4_1.
  rewrite Int.eq_true.
  rewrite Int.eq_true.
  rewrite Bool.andb_true_l.

  rewrite decode_arm32_ADD_I_OP_10_1.
  rewrite decode_arm32_ADD_I_OP_12_3; [| assumption].
  rewrite decode_arm32_ADD_I_OP_0_8; [| assumption].
  unfold thumb_constant_range_imm12.
  rewrite Int.eq_true, Hcmp.
  rewrite ! Bool.andb_true_l.
  rewrite decode_arm32_ADD_I_OP_dst2.
  replace (Int.eq (Int.repr 8) Int.zero) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 8) (Int.repr 2)) with false by reflexivity; simpl.

  unfold encode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in Hcmp.
  rewrite bitfield_insert_over_size_zero with (pos := 8%Z)(x := 8%Z); auto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  rewrite bitfield_insert_over_size_zero with (x := 8%Z); auto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
Qed.

Lemma decode_arm32_MOVW_OP_HI_11_5:
  forall si r,
  (decode_arm32
       (encode_arm32
          (encode_arm32 (decode_arm32 si 8 3) (encode_arm32 (int_of_ireg r) (decode_arm32 si 0 8) 8 4) 12 3)
          (encode_arm32 (decode_arm32 si 11 1) (encode_arm32 (decode_arm32 si 12 4) MOVW_OP 0 4) 10 1) 16 16) 11 5) = Int.repr 30.
Proof.
  intros.
  unfold MOVW_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 10%Z) (width0 := 1%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  auto.
Qed.

Lemma decode_arm32_MOVW_OP_LO_11_5:
  forall si r,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (decode_arm32 si 8 3) (encode_arm32 (int_of_ireg r) (decode_arm32 si 0 8) 8 4) 12 3)
             (encode_arm32 (decode_arm32 si 11 1) (encode_arm32 (decode_arm32 si 12 4) MOVW_OP 0 4) 10 1) 16 16) 0
          16) 11 5) =
    (Int.repr 30).
Proof.
  unfold MOVW_OP, decode_arm32, encode_arm32.
  intros.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite unsigned_bitfield_extract_low_same with (width := 16%Z);
    [ | replace Int.zwordsize with 32%Z by reflexivity; lia | ].

  - erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 10%Z) (width0 := 1%Z) (pos1 := 11%Z) (width1 := 5%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 11%Z) (width1 := 5%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    auto.
  - apply Int.bits_size_3; [lia |].
    intros i Hrange.
    rewrite Int.bits_bitfield_insert;
    replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
    destruct (_ && _) eqn: Hc.
    + rewrite Bool.andb_true_iff in Hc.
      rewrite <- zle_true_iff in Hc.
      rewrite <- zlt_true_iff in Hc.
      lia.
    + rewrite Int.bits_bitfield_insert;
      replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
      clear Hc.
      destruct (_ && _) eqn: Hd.
      * rewrite Bool.andb_true_iff in Hd.
        rewrite <- zle_true_iff in Hd.
        rewrite <- zlt_true_iff in Hd.
        lia.
      * apply Int.bits_size_2.
        prove_int.
Qed.

Lemma decode_arm32_MOVW_OP_15_1:
  forall si r,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (decode_arm32 si 8 3) (encode_arm32 (int_of_ireg r) (decode_arm32 si 0 8) 8 4) 12 3)
             (encode_arm32 (decode_arm32 si 11 1) (encode_arm32 (decode_arm32 si 12 4) MOVW_OP 0 4) 10 1) 16 16)
          16 16) 15 1) = Int.zero.
Proof.
  intros.
  unfold MOVW_OP, decode_arm32, encode_arm32.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + rewrite size_unsigned_bitfield_extract with (k := 16%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
      + destruct r; prove_int.
    - rewrite size_unsigned_bitfield_extract with (k := 3%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 12%Z) (width0 := 3%Z) (pos1 := 15%Z) (width1 := 1%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 15%Z) (width1 := 1%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite unsigned_bitfield_extract_unsigned_bitfield_extract_zero_outside with
    (pos0 := 0%Z) (width0 := 8%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [reflexivity | reflexivity].
Qed.

Lemma decode_arm32_MOVW_OP_5_4:
  forall si r,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (decode_arm32 si 8 3) (encode_arm32 (int_of_ireg r) (decode_arm32 si 0 8) 8 4) 12 3)
             (encode_arm32 (decode_arm32 si 11 1) (encode_arm32 (decode_arm32 si 12 4) MOVW_OP 0 4) 10 1) 16 16) 0
          16) 5 4) = (Int.repr 2).
Proof.
  intros.
  unfold MOVW_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite unsigned_bitfield_extract_low_same with (width := 16%Z);
    [ | replace Int.zwordsize with 32%Z by reflexivity; lia | ].

  - erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 10%Z) (width0 := 1%Z) (pos1 := 5%Z) (width1 := 4%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 5%Z) (width1 := 4%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    auto.
  - apply Int.bits_size_3; [lia |].
    intros i Hrange.
    rewrite Int.bits_bitfield_insert;
    replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
    destruct (_ && _) eqn: Hc.
    + rewrite Bool.andb_true_iff in Hc.
      rewrite <- zle_true_iff in Hc.
      rewrite <- zlt_true_iff in Hc.
      lia.
    + rewrite Int.bits_bitfield_insert;
      replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
      clear Hc.
      destruct (_ && _) eqn: Hd.
      * rewrite Bool.andb_true_iff in Hd.
        rewrite <- zle_true_iff in Hd.
        rewrite <- zlt_true_iff in Hd.
        lia.
      * apply Int.bits_size_2.
        prove_int.
Qed.

Lemma decode_arm32_MOVW_OP_dst:
  forall si r,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (decode_arm32 si 8 3) (encode_arm32 (int_of_ireg r) (decode_arm32 si 0 8) 8 4) 12 3)
             (encode_arm32 (decode_arm32 si 11 1) (encode_arm32 (decode_arm32 si 12 4) MOVW_OP 0 4) 10 1) 16 16)
          16 16) 8 4) = Some r.
Proof.
  intros.
  unfold MOVW_OP, decode_arm32, encode_arm32.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + rewrite size_unsigned_bitfield_extract with (k := 16%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
      + destruct r; prove_int.
    - rewrite size_unsigned_bitfield_extract with (k := 3%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 12%Z) (width0 := 3%Z) (pos1 := 8%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (v:= (int_of_ireg r));
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  - apply int2ireg_int_of_ireg_same.
  - destruct r; prove_int.
Qed.

Lemma decode_arm32_MOVW_OP_9_1:
  forall si r,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (decode_arm32 si 8 3) (encode_arm32 (int_of_ireg r) (decode_arm32 si 0 8) 8 4) 12 3)
             (encode_arm32 (decode_arm32 si 11 1) (encode_arm32 (decode_arm32 si 12 4) MOVW_OP 0 4) 10 1) 16 16) 0
          16) 9 1) = Int.one.
Proof.
  intros.
  unfold MOVW_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite unsigned_bitfield_extract_low_same with (width := 16%Z);
    [ | replace Int.zwordsize with 32%Z by reflexivity; lia | ].

  - erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 10%Z) (width0 := 1%Z) (pos1 := 9%Z) (width1 := 1%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 9%Z) (width1 := 1%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    auto.
  - apply Int.bits_size_3; [lia |].
    intros i Hrange.
    rewrite Int.bits_bitfield_insert;
    replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
    destruct (_ && _) eqn: Hc.
    + rewrite Bool.andb_true_iff in Hc.
      rewrite <- zle_true_iff in Hc.
      rewrite <- zlt_true_iff in Hc.
      lia.
    + rewrite Int.bits_bitfield_insert;
      replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
      clear Hc.
      destruct (_ && _) eqn: Hd.
      * rewrite Bool.andb_true_iff in Hd.
        rewrite <- zle_true_iff in Hd.
        rewrite <- zlt_true_iff in Hd.
        lia.
      * apply Int.bits_size_2.
        prove_int.
Qed.

Lemma decode_arm32_MOVW_OP_4_1:
  forall si r,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (decode_arm32 si 8 3) (encode_arm32 (int_of_ireg r) (decode_arm32 si 0 8) 8 4) 12 3)
             (encode_arm32 (decode_arm32 si 11 1) (encode_arm32 (decode_arm32 si 12 4) MOVW_OP 0 4) 10 1) 16 16) 0
          16) 4 1) = Int.zero.
Proof.
  intros.
  unfold MOVW_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite unsigned_bitfield_extract_low_same with (width := 16%Z);
    [ | replace Int.zwordsize with 32%Z by reflexivity; lia | ].

  - erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 10%Z) (width0 := 1%Z) (pos1 := 4%Z) (width1 := 1%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 4%Z) (width1 := 1%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    auto.
  - apply Int.bits_size_3; [lia |].
    intros i Hrange.
    rewrite Int.bits_bitfield_insert;
    replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
    destruct (_ && _) eqn: Hc.
    + rewrite Bool.andb_true_iff in Hc.
      rewrite <- zle_true_iff in Hc.
      rewrite <- zlt_true_iff in Hc.
      lia.
    + rewrite Int.bits_bitfield_insert;
      replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
      clear Hc.
      destruct (_ && _) eqn: Hd.
      * rewrite Bool.andb_true_iff in Hd.
        rewrite <- zle_true_iff in Hd.
        rewrite <- zlt_true_iff in Hd.
        lia.
      * apply Int.bits_size_2.
        prove_int.
Qed.

Lemma decode_arm32_MOVW_hi_zero:
  forall si r,
    (decode_arm32
       (encode_arm32
          (decode_arm32
             (decode_arm32
                (encode_arm32
                   (encode_arm32 (decode_arm32 si 8 3)
                      (encode_arm32 (int_of_ireg r) (decode_arm32 si 0 8) 8 4) 12 3)
                   (encode_arm32 (decode_arm32 si 11 1)
                      (encode_arm32 (decode_arm32 si 12 4) MOVW_OP 0 4) 10 1) 16 16) 0 16) 0 4)
          (encode_arm32
             (decode_arm32
                (decode_arm32
                   (encode_arm32
                      (encode_arm32 (decode_arm32 si 8 3)
                         (encode_arm32 (int_of_ireg r) (decode_arm32 si 0 8) 8 4) 12 3)
                      (encode_arm32 (decode_arm32 si 11 1)
                         (encode_arm32 (decode_arm32 si 12 4) MOVW_OP 0 4) 10 1) 16 16) 0 16) 10
                1)
             (encode_arm32
                (decode_arm32
                   (decode_arm32
                      (encode_arm32
                         (encode_arm32 (decode_arm32 si 8 3)
                            (encode_arm32 (int_of_ireg r) (decode_arm32 si 0 8) 8 4) 12 3)
                         (encode_arm32 (decode_arm32 si 11 1)
                            (encode_arm32 (decode_arm32 si 12 4) MOVW_OP 0 4) 10 1) 16 16) 16 16)
                   12 3)
                (decode_arm32
                   (decode_arm32
                      (encode_arm32
                         (encode_arm32 (decode_arm32 si 8 3)
                            (encode_arm32 (int_of_ireg r) (decode_arm32 si 0 8) 8 4) 12 3)
                         (encode_arm32 (decode_arm32 si 11 1)
                            (encode_arm32 (decode_arm32 si 12 4) MOVW_OP 0 4) 10 1) 16 16) 16 16)
                   0 8) 8 3) 11 1) 12 4) 16 16) = Int.zero.
Proof.
  unfold MOVW_OP, decode_arm32, encode_arm32.
  intros.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 12%Z) (width0 := 4%Z) (pos1 := 16%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 11%Z) (width0 := 1%Z) (pos1 := 16%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 3%Z) (pos1 := 16%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + rewrite size_unsigned_bitfield_extract with (k := 16%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
      + destruct r; prove_int.
    - rewrite size_unsigned_bitfield_extract with (k := 3%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 12%Z) (width0 := 3%Z) (pos1 := 0%Z) (width1 := 8%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 8%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite unsigned_bitfield_extract_unsigned_bitfield_extract_zero_outside with
    (pos0 := 0%Z) (width0 := 8%Z) (pos1 := 16%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [reflexivity | ].
  reflexivity.
Qed.

Lemma decode_movw:
  forall si r,
    decode_thumb (mov_int_to_movwt si r MOVW_OP) =
    Some (Pmovw r (Int.unsigned_bitfield_extract 0 16 si)).
Proof.
  unfold decode_thumb, mov_int_to_movwt; intros.
  rewrite decode_arm32_MOVW_OP_HI_11_5.
  replace (Int.eq (Int.repr 30) (Int.repr 23)) with false by reflexivity; simpl.

  unfold decode_thumb2.
  rewrite decode_arm32_MOVW_OP_LO_11_5.
  replace (Int.eq (Int.repr 30) (Int.repr 29)) with false by reflexivity; simpl.
  rewrite Int.eq_true.
  rewrite decode_arm32_MOVW_OP_15_1.
  rewrite Int.eq_true.
  rewrite decode_arm32_MOVW_OP_5_4.
  replace (Int.eq (Int.repr 2) (Int.repr 13)) with false by reflexivity.
  rewrite Bool.andb_false_l.
  rewrite decode_arm32_MOVW_OP_dst.
  rewrite decode_arm32_MOVW_OP_9_1.
  rewrite decode_arm32_MOVW_OP_4_1.
  rewrite ! Int.eq_true.
  rewrite Bool.andb_true_l.

  rewrite decode_arm32_MOVW_hi_zero.
  rewrite Int.eq_true.
  unfold encode_arm32, decode_arm32, MOVW_OP in *.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + rewrite size_unsigned_bitfield_extract with (k := 16%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
      + destruct r; prove_int.
    - rewrite size_unsigned_bitfield_extract with (k := 3%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 12%Z) (width0 := 3%Z) (pos1 := 0%Z) (width1 := 8%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 8%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 12%Z) (width := 3%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    rewrite size_unsigned_bitfield_extract with (k := 3%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
  }

  erewrite unsigned_bitfield_extract_low_same with (width := 16%Z);
    [ | replace Int.zwordsize with 32%Z by reflexivity; lia | ].
  2:{
    apply Int.bits_size_3; [lia |].
    intros i Hrange.
    rewrite Int.bits_bitfield_insert;
    replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
    destruct (_ && _) eqn: Hc.
    + rewrite Bool.andb_true_iff in Hc.
      rewrite <- zle_true_iff in Hc.
      rewrite <- zlt_true_iff in Hc.
      lia.
    + rewrite Int.bits_bitfield_insert;
      replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
      clear Hc.
      destruct (_ && _) eqn: Hd.
      * rewrite Bool.andb_true_iff in Hd.
        rewrite <- zle_true_iff in Hd.
        rewrite <- zlt_true_iff in Hd.
        lia.
      * apply Int.bits_size_2.
        prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 10%Z) (width0 := 1%Z) (pos1 := 0%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite unsigned_bitfield_extract_bitfield_insert_same;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  2:{ rewrite size_unsigned_bitfield_extract with (k := 1%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
  }
  erewrite unsigned_bitfield_extract_bitfield_insert_same;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  2:{ rewrite size_unsigned_bitfield_extract with (k := 4%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
  }

  erewrite unsigned_bitfield_extract_same;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  rewrite unsigned_bitfield_extract_extend with (pos := 8%Z) (width := 3%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  replace (8 + 3)%Z with 11%Z by lia.
  rewrite unsigned_bitfield_extract_extend with (pos := 11%Z) (width := 1%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  replace (11 + 1)%Z with 12%Z by lia.
  rewrite unsigned_bitfield_extract_extend with (pos := 12%Z) (width := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  replace (12 + 4)%Z with 16%Z by lia.
  f_equal.
Qed.

Lemma decode_arm32_MOVT_OP_HI_11_5:
  forall si r,
  (decode_arm32
       (encode_arm32
          (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 8 3)
             (encode_arm32 (int_of_ireg r) (decode_arm32 (decode_arm32 si 16 16) 0 8) 8 4) 12
             3)
          (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 11 1)
             (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 12 4) MOVT_OP 0 4) 10 1) 16 16)
       11 5) = Int.repr 30.
Proof.
  intros.
  unfold MOVT_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 10%Z) (width0 := 1%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  auto.
Qed.

Lemma decode_arm32_MOVT_OP_LO_11_5:
  forall si r,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 8 3)
                (encode_arm32 (int_of_ireg r) (decode_arm32 (decode_arm32 si 16 16) 0 8) 8 4)
                12 3)
             (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 11 1)
                (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 12 4) MOVT_OP 0 4) 10 1) 16
             16) 0 16) 11 5) =
    (Int.repr 30).
Proof.
  unfold MOVW_OP, decode_arm32, encode_arm32.
  intros.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite unsigned_bitfield_extract_low_same with (width := 16%Z);
    [ | replace Int.zwordsize with 32%Z by reflexivity; lia | ].

  - erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 10%Z) (width0 := 1%Z) (pos1 := 11%Z) (width1 := 5%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 11%Z) (width1 := 5%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    auto.
  - apply Int.bits_size_3; [lia |].
    intros i Hrange.
    rewrite Int.bits_bitfield_insert;
    replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
    destruct (_ && _) eqn: Hc.
    + rewrite Bool.andb_true_iff in Hc.
      rewrite <- zle_true_iff in Hc.
      rewrite <- zlt_true_iff in Hc.
      lia.
    + rewrite Int.bits_bitfield_insert;
      replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
      clear Hc.
      destruct (_ && _) eqn: Hd.
      * rewrite Bool.andb_true_iff in Hd.
        rewrite <- zle_true_iff in Hd.
        rewrite <- zlt_true_iff in Hd.
        lia.
      * apply Int.bits_size_2.
        prove_int.
Qed.

Lemma decode_arm32_MOVT_OP_15_1:
  forall si r,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 8 3)
                (encode_arm32 (int_of_ireg r) (decode_arm32 (decode_arm32 si 16 16) 0 8) 8 4)
                12 3)
             (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 11 1)
                (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 12 4) MOVT_OP 0 4) 10 1) 16
             16) 16 16) 15 1) = Int.zero.
Proof.
  intros.
  unfold MOVT_OP, decode_arm32, encode_arm32.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + rewrite size_unsigned_bitfield_extract with (k := 16%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
      + destruct r; prove_int.
    - rewrite size_unsigned_bitfield_extract with (k := 3%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 12%Z) (width0 := 3%Z) (pos1 := 15%Z) (width1 := 1%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 15%Z) (width1 := 1%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite unsigned_bitfield_extract_unsigned_bitfield_extract_zero_outside with
    (pos0 := 0%Z) (width0 := 8%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [reflexivity | reflexivity].
Qed.

Lemma decode_arm32_MOVT_OP_5_4:
  forall si r,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 8 3)
                (encode_arm32 (int_of_ireg r) (decode_arm32 (decode_arm32 si 16 16) 0 8) 8 4)
                12 3)
             (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 11 1)
                (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 12 4) MOVT_OP 0 4) 10 1) 16
             16) 0 16) 5 4) = (Int.repr 6).
Proof.
  intros.
  unfold MOVT_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite unsigned_bitfield_extract_low_same with (width := 16%Z);
    [ | replace Int.zwordsize with 32%Z by reflexivity; lia | ].

  - erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 10%Z) (width0 := 1%Z) (pos1 := 5%Z) (width1 := 4%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 5%Z) (width1 := 4%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    auto.
  - apply Int.bits_size_3; [lia |].
    intros i Hrange.
    rewrite Int.bits_bitfield_insert;
    replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
    destruct (_ && _) eqn: Hc.
    + rewrite Bool.andb_true_iff in Hc.
      rewrite <- zle_true_iff in Hc.
      rewrite <- zlt_true_iff in Hc.
      lia.
    + rewrite Int.bits_bitfield_insert;
      replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
      clear Hc.
      destruct (_ && _) eqn: Hd.
      * rewrite Bool.andb_true_iff in Hd.
        rewrite <- zle_true_iff in Hd.
        rewrite <- zlt_true_iff in Hd.
        lia.
      * apply Int.bits_size_2.
        prove_int.
Qed.

Lemma decode_arm32_MOVT_OP_dst:
  forall si r,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 8 3)
                (encode_arm32 (int_of_ireg r) (decode_arm32 (decode_arm32 si 16 16) 0 8) 8 4)
                12 3)
             (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 11 1)
                (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 12 4) MOVT_OP 0 4) 10 1) 16
             16) 16 16) 8 4) = Some r.
Proof.
  intros.
  unfold MOVT_OP, decode_arm32, encode_arm32.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + rewrite size_unsigned_bitfield_extract with (k := 16%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
      + destruct r; prove_int.
    - rewrite size_unsigned_bitfield_extract with (k := 3%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 12%Z) (width0 := 3%Z) (pos1 := 8%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (v:= (int_of_ireg r));
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  - apply int2ireg_int_of_ireg_same.
  - destruct r; prove_int.
Qed.

Lemma decode_arm32_MOVT_OP_9_1:
  forall si r,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 8 3)
                (encode_arm32 (int_of_ireg r) (decode_arm32 (decode_arm32 si 16 16) 0 8) 8 4)
                12 3)
             (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 11 1)
                (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 12 4) MOVT_OP 0 4) 10 1) 16
             16) 0 16) 9 1) = Int.one.
Proof.
  intros.
  unfold MOVT_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite unsigned_bitfield_extract_low_same with (width := 16%Z);
    [ | replace Int.zwordsize with 32%Z by reflexivity; lia | ].

  - erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 10%Z) (width0 := 1%Z) (pos1 := 9%Z) (width1 := 1%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 9%Z) (width1 := 1%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    auto.
  - apply Int.bits_size_3; [lia |].
    intros i Hrange.
    rewrite Int.bits_bitfield_insert;
    replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
    destruct (_ && _) eqn: Hc.
    + rewrite Bool.andb_true_iff in Hc.
      rewrite <- zle_true_iff in Hc.
      rewrite <- zlt_true_iff in Hc.
      lia.
    + rewrite Int.bits_bitfield_insert;
      replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
      clear Hc.
      destruct (_ && _) eqn: Hd.
      * rewrite Bool.andb_true_iff in Hd.
        rewrite <- zle_true_iff in Hd.
        rewrite <- zlt_true_iff in Hd.
        lia.
      * apply Int.bits_size_2.
        prove_int.
Qed.

Lemma decode_arm32_MOVT_OP_4_1:
  forall si r,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 8 3)
                (encode_arm32 (int_of_ireg r) (decode_arm32 (decode_arm32 si 16 16) 0 8) 8 4)
                12 3)
             (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 11 1)
                (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 12 4) MOVT_OP 0 4) 10 1) 16
             16) 0 16) 4 1) = Int.zero.
Proof.
  intros.
  unfold MOVT_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite unsigned_bitfield_extract_low_same with (width := 16%Z);
    [ | replace Int.zwordsize with 32%Z by reflexivity; lia | ].

  - erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 10%Z) (width0 := 1%Z) (pos1 := 4%Z) (width1 := 1%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 4%Z) (width1 := 1%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    auto.
  - apply Int.bits_size_3; [lia |].
    intros i Hrange.
    rewrite Int.bits_bitfield_insert;
    replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
    destruct (_ && _) eqn: Hc.
    + rewrite Bool.andb_true_iff in Hc.
      rewrite <- zle_true_iff in Hc.
      rewrite <- zlt_true_iff in Hc.
      lia.
    + rewrite Int.bits_bitfield_insert;
      replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
      clear Hc.
      destruct (_ && _) eqn: Hd.
      * rewrite Bool.andb_true_iff in Hd.
        rewrite <- zle_true_iff in Hd.
        rewrite <- zlt_true_iff in Hd.
        lia.
      * apply Int.bits_size_2.
        prove_int.
Qed.

Lemma decode_arm32_MOVT_hi_zero:
  forall si r,
    (decode_arm32
       (encode_arm32
          (decode_arm32
             (decode_arm32
                (encode_arm32
                   (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 8 3)
                      (encode_arm32 (int_of_ireg r) (decode_arm32 (decode_arm32 si 16 16) 0 8)
                         8 4) 12 3)
                   (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 11 1)
                      (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 12 4) MOVT_OP 0 4) 10 1)
                   16 16) 0 16) 0 4)
          (encode_arm32
             (decode_arm32
                (decode_arm32
                   (encode_arm32
                      (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 8 3)
                         (encode_arm32 (int_of_ireg r)
                            (decode_arm32 (decode_arm32 si 16 16) 0 8) 8 4) 12 3)
                      (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 11 1)
                         (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 12 4) MOVT_OP 0 4)
                         10 1) 16 16) 0 16) 10 1)
             (encode_arm32
                (decode_arm32
                   (decode_arm32
                      (encode_arm32
                         (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 8 3)
                            (encode_arm32 (int_of_ireg r)
                               (decode_arm32 (decode_arm32 si 16 16) 0 8) 8 4) 12 3)
                         (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 11 1)
                            (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 12 4) MOVT_OP 0 4)
                            10 1) 16 16) 16 16) 12 3)
                (decode_arm32
                   (decode_arm32
                      (encode_arm32
                         (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 8 3)
                            (encode_arm32 (int_of_ireg r)
                               (decode_arm32 (decode_arm32 si 16 16) 0 8) 8 4) 12 3)
                         (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 11 1)
                            (encode_arm32 (decode_arm32 (decode_arm32 si 16 16) 12 4) MOVT_OP 0 4)
                            10 1) 16 16) 16 16) 0 8) 8 3) 11 1) 12 4) 16 16) = Int.zero.
Proof.
  unfold MOVT_OP, decode_arm32, encode_arm32.
  intros.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 12%Z) (width0 := 4%Z) (pos1 := 16%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 11%Z) (width0 := 1%Z) (pos1 := 16%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 3%Z) (pos1 := 16%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + rewrite size_unsigned_bitfield_extract with (k := 16%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
      + destruct r; prove_int.
    - rewrite size_unsigned_bitfield_extract with (k := 3%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 12%Z) (width0 := 3%Z) (pos1 := 0%Z) (width1 := 8%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 8%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite unsigned_bitfield_extract_unsigned_bitfield_extract_zero_outside with
    (pos0 := 0%Z) (width0 := 8%Z) (pos1 := 16%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [reflexivity | ].
  reflexivity.
Qed.

Lemma decode_movt:
  forall si r,
    decode_thumb (mov_int_to_movwt (decode_arm32 si 16 16) r MOVT_OP) =
    Some (Pmovt r (Int.unsigned_bitfield_extract 16 16 si)).
Proof.
  unfold decode_thumb, mov_int_to_movwt; intros.
  rewrite decode_arm32_MOVT_OP_HI_11_5.
  replace (Int.eq (Int.repr 30) (Int.repr 23)) with false by reflexivity; simpl.

  unfold decode_thumb2.
  rewrite decode_arm32_MOVT_OP_LO_11_5.
  replace (Int.eq (Int.repr 30) (Int.repr 29)) with false by reflexivity; simpl.
  rewrite Int.eq_true.
  rewrite decode_arm32_MOVT_OP_15_1.
  rewrite Int.eq_true.
  rewrite decode_arm32_MOVT_OP_5_4.
  replace (Int.eq (Int.repr 6) (Int.repr 13)) with false by reflexivity.
  rewrite Bool.andb_false_l.
  rewrite decode_arm32_MOVT_OP_dst.
  rewrite decode_arm32_MOVT_OP_9_1.
  rewrite decode_arm32_MOVT_OP_4_1.
  rewrite ! Int.eq_true.
  rewrite Bool.andb_true_l.
  replace (Int.eq (Int.repr 6) (Int.repr 2)) with false by reflexivity.

  rewrite decode_arm32_MOVT_hi_zero.
  rewrite Int.eq_true.
  unfold encode_arm32, decode_arm32, MOVT_OP in *.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + rewrite size_unsigned_bitfield_extract with (k := 16%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
      + destruct r; prove_int.
    - rewrite size_unsigned_bitfield_extract with (k := 3%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 12%Z) (width0 := 3%Z) (pos1 := 0%Z) (width1 := 8%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 8%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 12%Z) (width := 3%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    rewrite size_unsigned_bitfield_extract with (k := 3%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
  }

  erewrite unsigned_bitfield_extract_low_same with (width := 16%Z);
    [ | replace Int.zwordsize with 32%Z by reflexivity; lia | ].
  2:{
    apply Int.bits_size_3; [lia |].
    intros i Hrange.
    rewrite Int.bits_bitfield_insert;
    replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
    destruct (_ && _) eqn: Hc.
    + rewrite Bool.andb_true_iff in Hc.
      rewrite <- zle_true_iff in Hc.
      rewrite <- zlt_true_iff in Hc.
      lia.
    + rewrite Int.bits_bitfield_insert;
      replace Int.zwordsize with 32%Z in * by reflexivity; try lia.
      clear Hc.
      destruct (_ && _) eqn: Hd.
      * rewrite Bool.andb_true_iff in Hd.
        rewrite <- zle_true_iff in Hd.
        rewrite <- zlt_true_iff in Hd.
        lia.
      * apply Int.bits_size_2.
        prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 10%Z) (width0 := 1%Z) (pos1 := 0%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite unsigned_bitfield_extract_bitfield_insert_same;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  2:{ rewrite size_unsigned_bitfield_extract with (k := 1%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
  }
  erewrite unsigned_bitfield_extract_bitfield_insert_same;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  2:{ rewrite size_unsigned_bitfield_extract with (k := 4%Z);
        replace Int.zwordsize with 32%Z by reflexivity; try lia.
  }

  erewrite unsigned_bitfield_extract_same;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  rewrite unsigned_bitfield_extract_extend with (pos := 8%Z) (width := 3%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  replace (8 + 3)%Z with 11%Z by lia.
  rewrite unsigned_bitfield_extract_extend with (pos := 11%Z) (width := 1%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  replace (11 + 1)%Z with 12%Z by lia.
  rewrite unsigned_bitfield_extract_extend with (pos := 12%Z) (width := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  replace (12 + 4)%Z with 16%Z by lia.
  rewrite unsigned_bitfield_extract_unchange;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  simpl.
  f_equal.
Qed.


Lemma decode_arm32_0_16_16_equal:
  forall si,
  (Int.or (Int.and (decode_arm32 si 0 16) (Int.repr 65535))
                      (Int.shl (Int.unsigned_bitfield_extract 16 16 si) (Int.repr 16))) = si.
Proof.
  intros.
  assert (Heq: (Int.or (Int.and (decode_arm32 si 0 16) (Int.repr 65535))
                      (Int.shl (Int.unsigned_bitfield_extract 16 16 si) (Int.repr 16))) =
    Int.bitfield_insert 16 16 (decode_arm32 si 0 16) (Int.unsigned_bitfield_extract 16 16 si)). {
    unfold Int.bitfield_insert.
    rewrite Int.or_commut.
    assert (Heq: (Int.unsigned_bitfield_extract 16 16 si) =
      (Int.zero_ext 16 (Int.unsigned_bitfield_extract 16 16 si))). {
      unfold Int.unsigned_bitfield_extract.
      rewrite Int.zero_ext_idem. f_equal. lia.
    }
    rewrite <- Heq; clear Heq.
    replace (Int.not (Int.shl (Int.repr (two_p 16 - 1)) (Int.repr 16))) with (Int.repr 65535) by reflexivity.
    f_equal.
  }
  rewrite Heq; clear Heq.
  assert (Heq: Int.bitfield_insert 16 16 (decode_arm32 si 0 16)
    (Int.unsigned_bitfield_extract 16 16 si) = si). {
    unfold decode_arm32.
    erewrite unsigned_bitfield_extract_extend;
      replace Int.zwordsize with 32%Z by reflexivity; try lia.
    simpl.
    unfold Int.unsigned_bitfield_extract.
    fold Int.zero; rewrite Int.shru_zero.
    rewrite Int.zero_ext_above.
    reflexivity.
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  }
  rewrite Heq; clear Heq.
  reflexivity.
Qed.

Lemma decode_arm32_SUB_I_OP_LO_11_5:
  forall dst si,
    (decode_arm32
         (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
            (encode_arm32 (int_of_breg dst) SUB_I_OP 0 4) 16 16) 11 5) = Int.repr 30.
Proof.
  intros.
  unfold SUB_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  auto.
Qed.

Lemma decode_arm32_SUB_I_OP_HI_11_5:
  forall dst si,
  (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) SUB_I_OP 0 4) 16 16) 0 16) 11 5) = Int.repr 30.
Proof.
  intros.
  unfold SUB_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_SUB_I_OP_15_1:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    (decode_arm32
         (decode_arm32
            (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
               (encode_arm32 (int_of_breg dst) SUB_I_OP 0 4) 16 16) 16 16) 15 1) =
        Int.zero.
Proof.
  intros.
  unfold SUB_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 15%Z) (width1 := 1%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  eapply unsigned_bitfield_extract_over_size; eauto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
Qed.

Lemma decode_arm32_SUB_I_OP_5_4:
  forall dst si,
   (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) SUB_I_OP 0 4) 16 16) 0 16) 5 4) = (Int.repr 13).
Proof.
  intros.
  unfold SUB_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_SUB_I_OP_9_1:
  forall dst si,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) SUB_I_OP 0 4) 16 16) 0 16) 9 1) =
        Int.zero.
Proof.
  intros.
  unfold SUB_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_SUB_I_OP_4_1:
  forall dst si,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) SUB_I_OP 0 4) 16 16) 0 16) 4 1) =
        Int.zero.
Proof.
  intros.
  unfold SUB_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_SUB_I_OP_dst:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) SUB_I_OP 0 4) 16 16) 16 16) 8 4) =
        Some (ireg_of_breg dst).
Proof.
  intros.
  unfold SUB_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 8%Z) (width := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{ unfold int_of_breg; destruct dst; prove_int. }

  apply int2ireg_int_of_breg_same; auto.
Qed.

Lemma decode_arm32_SUB_I_OP_10_1:
  forall dst si,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) SUB_I_OP 0 4) 16
             16) 0 16) 10 1) =
        Int.zero.
Proof.
  intros.
  unfold SUB_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_SUB_I_OP_12_3:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) SUB_I_OP 0 4) 16
             16) 16 16) 12 3) =
        Int.zero.
Proof.
  intros.
  unfold SUB_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 12%Z) (width1 := 3%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  eapply unsigned_bitfield_extract_over_size; eauto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
Qed.

Lemma decode_arm32_SUB_I_OP_0_8:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) SUB_I_OP 0 4) 16
             16) 16 16) 0 8) = si.
Proof.
  intros.
  unfold SUB_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 8%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  apply unsigned_bitfield_extract_low_same; auto.
  replace Int.zwordsize with 32%Z by reflexivity; lia.
Qed.

Lemma decode_arm32_SUB_I_OP_dst2:
  forall dst si,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) SUB_I_OP 0 4) 16
             16) 0 16) 0 4) = Some (ireg_of_breg dst).
Proof.
  intros.
  unfold SUB_I_OP, NOP_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_sub_i:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    decode_thumb
      (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) SUB_I_OP 0 4) 16 16) =
      Some (Psub (ireg_of_breg dst) (ireg_of_breg dst)
                (SOimm si)).
Proof.
  intros dst si Hcmp.
  unfold decode_thumb.
  rewrite decode_arm32_SUB_I_OP_LO_11_5.
  replace (Int.eq (Int.repr 30) (Int.repr 23)) with false by reflexivity.
  unfold decode_thumb2.
  rewrite decode_arm32_SUB_I_OP_HI_11_5.
  replace (Int.eq (Int.repr 30) (Int.repr 29)) with false by reflexivity.
  rewrite Int.eq_true.
  rewrite decode_arm32_SUB_I_OP_15_1; [| assumption].
  rewrite Int.eq_true.
  rewrite decode_arm32_SUB_I_OP_5_4.
  rewrite decode_arm32_SUB_I_OP_9_1.
  rewrite decode_arm32_SUB_I_OP_4_1.
  replace (Int.eq Int.zero Int.one) with false by reflexivity.
  rewrite Bool.andb_false_r.

  rewrite decode_arm32_SUB_I_OP_dst; [| assumption].
  rewrite Bool.andb_false_l.
  rewrite Int.eq_true.
  rewrite Bool.andb_true_l.

  rewrite decode_arm32_SUB_I_OP_10_1.
  rewrite decode_arm32_SUB_I_OP_12_3; [| assumption].
  rewrite decode_arm32_SUB_I_OP_0_8; [| assumption].
  unfold thumb_constant_range_imm12.
  rewrite Int.eq_true, Hcmp.
  rewrite ! Bool.andb_true_l.
  rewrite decode_arm32_SUB_I_OP_dst2.
  replace (Int.eq (Int.repr 13) Int.zero) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 13) (Int.repr 2)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 13) (Int.repr 4)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 13) (Int.repr 8)) with false by reflexivity; simpl.
  rewrite Int.eq_true.

  unfold encode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in Hcmp.
  rewrite bitfield_insert_over_size_zero with (pos := 8%Z)(x := 8%Z); auto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  rewrite bitfield_insert_over_size_zero with (x := 8%Z); auto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
Qed.

Lemma decode_arm32_ORR_I_OP_LO_11_5:
  forall dst si,
    (decode_arm32
         (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
            (encode_arm32 (int_of_breg dst) ORR_I_OP 0 4) 16 16) 11 5) = Int.repr 30.
Proof.
  intros.
  unfold ORR_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  auto.
Qed.

Lemma decode_arm32_ORR_I_OP_HI_11_5:
  forall dst si,
  (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) ORR_I_OP 0 4) 16 16) 0 16) 11 5) = Int.repr 30.
Proof.
  intros.
  unfold ORR_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_ORR_I_OP_15_1:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    (decode_arm32
         (decode_arm32
            (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
               (encode_arm32 (int_of_breg dst) ORR_I_OP 0 4) 16 16) 16 16) 15 1) =
        Int.zero.
Proof.
  intros.
  unfold ORR_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 15%Z) (width1 := 1%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  eapply unsigned_bitfield_extract_over_size; eauto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
Qed.

Lemma decode_arm32_ORR_I_OP_5_4:
  forall dst si,
   (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) ORR_I_OP 0 4) 16 16) 0 16) 5 4) = (Int.repr 2).
Proof.
  intros.
  unfold ORR_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_ORR_I_OP_9_1:
  forall dst si,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) ORR_I_OP 0 4) 16 16) 0 16) 9 1) =
        Int.zero.
Proof.
  intros.
  unfold ORR_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_ORR_I_OP_4_1:
  forall dst si,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) ORR_I_OP 0 4) 16 16) 0 16) 4 1) =
        Int.zero.
Proof.
  intros.
  unfold ORR_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_ORR_I_OP_dst:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) ORR_I_OP 0 4) 16 16) 16 16) 8 4) =
        Some (ireg_of_breg dst).
Proof.
  intros.
  unfold ORR_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 8%Z) (width := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{ unfold int_of_breg; destruct dst; prove_int. }

  apply int2ireg_int_of_breg_same; auto.
Qed.

Lemma decode_arm32_ORR_I_OP_10_1:
  forall dst si,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) ORR_I_OP 0 4) 16
             16) 0 16) 10 1) =
        Int.zero.
Proof.
  intros.
  unfold ORR_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_ORR_I_OP_12_3:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) ORR_I_OP 0 4) 16
             16) 16 16) 12 3) =
        Int.zero.
Proof.
  intros.
  unfold ORR_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 12%Z) (width1 := 3%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  eapply unsigned_bitfield_extract_over_size; eauto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
Qed.

Lemma decode_arm32_ORR_I_OP_0_8:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) ORR_I_OP 0 4) 16
             16) 16 16) 0 8) = si.
Proof.
  intros.
  unfold ORR_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 8%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  apply unsigned_bitfield_extract_low_same; auto.
  replace Int.zwordsize with 32%Z by reflexivity; lia.
Qed.

Lemma decode_arm32_ORR_I_OP_dst2:
  forall dst si,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) ORR_I_OP 0 4) 16
             16) 0 16) 0 4) = Some (ireg_of_breg dst).
Proof.
  intros.
  unfold ORR_I_OP, NOP_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_orr_i:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    decode_thumb
      (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) ORR_I_OP 0 4) 16 16) =
      Some (Porr (ireg_of_breg dst) (ireg_of_breg dst)
                (SOimm si)).
Proof.
  intros dst si Hcmp.
  unfold decode_thumb.
  rewrite decode_arm32_ORR_I_OP_LO_11_5.
  replace (Int.eq (Int.repr 30) (Int.repr 23)) with false by reflexivity.
  unfold decode_thumb2.
  rewrite decode_arm32_ORR_I_OP_HI_11_5.
  replace (Int.eq (Int.repr 30) (Int.repr 29)) with false by reflexivity.
  rewrite Int.eq_true.
  rewrite decode_arm32_ORR_I_OP_15_1; [| assumption].
  rewrite Int.eq_true.
  rewrite decode_arm32_ORR_I_OP_5_4.
  replace (Int.eq (Int.repr 2) (Int.repr 13)) with false by reflexivity; simpl.
  rewrite decode_arm32_ORR_I_OP_dst; [| assumption].

  rewrite decode_arm32_ORR_I_OP_9_1.
  replace (Int.eq Int.zero Int.one) with false by reflexivity.
  rewrite Bool.andb_false_l.
  rewrite decode_arm32_ORR_I_OP_4_1.
  rewrite Int.eq_true.
  rewrite Bool.andb_true_l.

  rewrite decode_arm32_ORR_I_OP_10_1.
  rewrite decode_arm32_ORR_I_OP_12_3; [| assumption].
  rewrite decode_arm32_ORR_I_OP_0_8; [| assumption].
  unfold thumb_constant_range_imm12.
  rewrite Int.eq_true, Hcmp.
  rewrite ! Bool.andb_true_l.
  rewrite decode_arm32_ORR_I_OP_dst2.
  replace (Int.eq (Int.repr 2) Int.zero) with false by reflexivity; simpl.
  rewrite Int.eq_true.

  unfold encode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in Hcmp.
  rewrite bitfield_insert_over_size_zero with (pos := 8%Z)(x := 8%Z); auto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  rewrite bitfield_insert_over_size_zero with (x := 8%Z); auto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
Qed.

Lemma decode_arm32_AND_I_OP_LO_11_5:
  forall dst si,
    (decode_arm32
         (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
            (encode_arm32 (int_of_breg dst) AND_I_OP 0 4) 16 16) 11 5) = Int.repr 30.
Proof.
  intros.
  unfold AND_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  auto.
Qed.

Lemma decode_arm32_AND_I_OP_HI_11_5:
  forall dst si,
  (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) AND_I_OP 0 4) 16 16) 0 16) 11 5) = Int.repr 30.
Proof.
  intros.
  unfold AND_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_AND_I_OP_15_1:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    (decode_arm32
         (decode_arm32
            (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
               (encode_arm32 (int_of_breg dst) AND_I_OP 0 4) 16 16) 16 16) 15 1) =
        Int.zero.
Proof.
  intros.
  unfold AND_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 15%Z) (width1 := 1%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  eapply unsigned_bitfield_extract_over_size; eauto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
Qed.

Lemma decode_arm32_AND_I_OP_5_4:
  forall dst si,
   (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) AND_I_OP 0 4) 16 16) 0 16) 5 4) = Int.zero.
Proof.
  intros.
  unfold AND_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_AND_I_OP_9_1:
  forall dst si,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) AND_I_OP 0 4) 16 16) 0 16) 9 1) =
        Int.zero.
Proof.
  intros.
  unfold AND_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_AND_I_OP_4_1:
  forall dst si,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) AND_I_OP 0 4) 16 16) 0 16) 4 1) =
        Int.zero.
Proof.
  intros.
  unfold AND_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_AND_I_OP_dst:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
             (encode_arm32 (int_of_breg dst) AND_I_OP 0 4) 16 16) 16 16) 8 4) =
        Some (ireg_of_breg dst).
Proof.
  intros.
  unfold AND_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 8%Z) (width := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{ unfold int_of_breg; destruct dst; prove_int. }

  apply int2ireg_int_of_breg_same; auto.
Qed.

Lemma decode_arm32_AND_I_OP_10_1:
  forall dst si,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) AND_I_OP 0 4) 16
             16) 0 16) 10 1) =
        Int.zero.
Proof.
  intros.
  unfold AND_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_AND_I_OP_12_3:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) AND_I_OP 0 4) 16
             16) 16 16) 12 3) =
        Int.zero.
Proof.
  intros.
  unfold AND_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 12%Z) (width1 := 3%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  eapply unsigned_bitfield_extract_over_size; eauto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
Qed.

Lemma decode_arm32_AND_I_OP_0_8:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) AND_I_OP 0 4) 16
             16) 16 16) 0 8) = si.
Proof.
  intros.
  unfold AND_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 8%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  apply unsigned_bitfield_extract_low_same; auto.
  replace Int.zwordsize with 32%Z by reflexivity; lia.
Qed.

Lemma decode_arm32_AND_I_OP_dst2:
  forall dst si,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) AND_I_OP 0 4) 16
             16) 0 16) 0 4) = Some (ireg_of_breg dst).
Proof.
  intros.
  unfold AND_I_OP, NOP_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_and_i:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    decode_thumb
      (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) AND_I_OP 0 4) 16 16) =
      Some (Pand (ireg_of_breg dst) (ireg_of_breg dst)
                (SOimm si)).
Proof.
  intros dst si Hcmp.
  unfold decode_thumb.
  rewrite decode_arm32_AND_I_OP_LO_11_5.
  replace (Int.eq (Int.repr 30) (Int.repr 23)) with false by reflexivity.
  unfold decode_thumb2.
  rewrite decode_arm32_AND_I_OP_HI_11_5.
  replace (Int.eq (Int.repr 30) (Int.repr 29)) with false by reflexivity.
  rewrite Int.eq_true.
  rewrite decode_arm32_AND_I_OP_15_1; [| assumption].
  rewrite Int.eq_true.
  rewrite decode_arm32_AND_I_OP_5_4.
  replace (Int.eq Int.zero (Int.repr 13)) with false by reflexivity.
  rewrite Bool.andb_false_l.

  rewrite decode_arm32_AND_I_OP_dst; [| assumption].
  rewrite decode_arm32_AND_I_OP_9_1.
  replace (Int.eq Int.zero Int.one) with false by reflexivity.
  rewrite Bool.andb_false_l.
  rewrite decode_arm32_AND_I_OP_4_1.
  rewrite Int.eq_true.
  rewrite Bool.andb_true_l.

  rewrite decode_arm32_AND_I_OP_10_1.
  rewrite decode_arm32_AND_I_OP_12_3; [| assumption].
  rewrite decode_arm32_AND_I_OP_0_8; [| assumption].
  unfold thumb_constant_range_imm12.
  rewrite Int.eq_true, Hcmp.
  rewrite ! Bool.andb_true_l.
  rewrite decode_arm32_AND_I_OP_dst2.

  unfold encode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in Hcmp.
  rewrite bitfield_insert_over_size_zero with (pos := 8%Z)(x := 8%Z); auto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  rewrite bitfield_insert_over_size_zero with (x := 8%Z); auto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
Qed.

Lemma decode_arm32_RSB_I_OP_LO_11_5:
  forall dst src,
    (decode_arm32
       (encode_arm32 (encode_arm32 (int_of_breg dst) Int.zero 8 4) (encode_arm32 (int_of_ireg src) RSB_I_OP 0 4)
          16 16) 11 5) = Int.repr 30.
Proof.
  intros.
  unfold RSB_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  auto.
Qed.

Lemma decode_arm32_RSB_I_OP_HI_11_5:
  forall dst src,
  (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) Int.zero 8 4)
             (encode_arm32 (int_of_ireg src) RSB_I_OP 0 4) 16 16) 0 16) 11 5) = Int.repr 30.
Proof.
  intros.
  unfold RSB_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct src; auto.
Qed.

Lemma decode_arm32_RSB_I_OP_15_1:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) Int.zero 8 4)
             (encode_arm32 (int_of_ireg src) RSB_I_OP 0 4) 16 16) 16 16) 15 1) =
        Int.zero.
Proof.
  intros.
  unfold RSB_I_OP, decode_arm32, encode_arm32.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 15%Z) (width1 := 1%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  auto.
Qed.

Lemma decode_arm32_RSB_I_OP_5_4:
  forall dst src,
   (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) Int.zero 8 4)
             (encode_arm32 (int_of_ireg src) RSB_I_OP 0 4) 16 16) 0 16) 5 4) = (Int.repr 14).
Proof.
  intros.
  unfold RSB_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct src; auto.
Qed.

Lemma decode_arm32_RSB_I_OP_dst:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) Int.zero 8 4)
             (encode_arm32 (int_of_ireg src) RSB_I_OP 0 4) 16 16) 16 16) 8 4) =
        Some (ireg_of_breg dst).
Proof.
  intros.
  unfold RSB_I_OP, decode_arm32, encode_arm32.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 8%Z) (width := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{ unfold int_of_breg; destruct dst; prove_int. }

  apply int2ireg_int_of_breg_same; auto.
Qed.

Lemma decode_arm32_RSB_I_OP_9_1:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) Int.zero 8 4)
             (encode_arm32 (int_of_ireg src) RSB_I_OP 0 4) 16 16) 0 16) 9 1) =
        Int.zero.
Proof.
  intros.
  unfold RSB_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct src; auto.
Qed.

Lemma decode_arm32_RSB_I_OP_4_1:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) Int.zero 8 4)
             (encode_arm32 (int_of_ireg src) RSB_I_OP 0 4) 16 16) 0 16) 4 1) =
        Int.zero.
Proof.
  intros.
  unfold RSB_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct src; auto.
Qed.

Lemma decode_arm32_RSB_I_OP_10_1:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) Int.zero 8 4)
             (encode_arm32 (int_of_ireg src) RSB_I_OP 0 4) 16 16) 0 16) 10 1) =
        Int.zero.
Proof.
  intros.
  unfold RSB_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct src; auto.
Qed.

Lemma decode_arm32_RSB_I_OP_12_3:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) Int.zero 8 4)
             (encode_arm32 (int_of_ireg src) RSB_I_OP 0 4) 16 16) 16 16) 12 3) =
        Int.zero.
Proof.
  intros.
  unfold RSB_I_OP, decode_arm32, encode_arm32.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 12%Z) (width1 := 3%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  auto.
Qed.

Lemma decode_arm32_RSB_I_OP_0_8:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) Int.zero 8 4)
             (encode_arm32 (int_of_ireg src) RSB_I_OP 0 4) 16 16) 16 16) 0 8) = Int.zero.
Proof.
  intros.
  unfold RSB_I_OP, decode_arm32, encode_arm32.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 8%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  auto.
Qed.

Lemma decode_arm32_RSB_I_OP_dst2:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) Int.zero 8 4)
             (encode_arm32 (int_of_ireg src) RSB_I_OP 0 4) 16 16) 0 16) 0 4) = Some src.
Proof.
  intros.
  unfold RSB_I_OP, NOP_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct src; auto.
Qed.

Lemma decode_rsb_r:
  forall dst src,
    decode_thumb
      (encode_arm32 (encode_arm32 (int_of_breg dst) Int.zero 8 4) (encode_arm32 (int_of_ireg src) RSB_I_OP 0 4)
         16 16) = Some (Prsb (ireg_of_breg dst) src (SOimm Int.zero)).
Proof.
  intros.
  unfold decode_thumb.
  rewrite decode_arm32_RSB_I_OP_LO_11_5.
  replace (Int.eq (Int.repr 30) (Int.repr 23)) with false by reflexivity.
  unfold decode_thumb2.
  rewrite decode_arm32_RSB_I_OP_HI_11_5.
  replace (Int.eq (Int.repr 30) (Int.repr 29)) with false by reflexivity.
  rewrite Int.eq_true.
  rewrite decode_arm32_RSB_I_OP_15_1.
  rewrite Int.eq_true.
  rewrite decode_arm32_RSB_I_OP_5_4.
  replace (Int.eq (Int.repr 14) (Int.repr 13)) with false by reflexivity.
  rewrite Bool.andb_false_l.

  rewrite decode_arm32_RSB_I_OP_dst.
  rewrite decode_arm32_RSB_I_OP_9_1.
  replace (Int.eq Int.zero Int.one) with false by reflexivity.
  rewrite Bool.andb_false_l.
  rewrite decode_arm32_RSB_I_OP_4_1.
  rewrite Int.eq_true.
  rewrite Bool.andb_true_l.

  rewrite decode_arm32_RSB_I_OP_10_1.
  rewrite decode_arm32_RSB_I_OP_12_3.
  rewrite decode_arm32_RSB_I_OP_0_8.
  unfold thumb_constant_range_imm12.
  rewrite Int.eq_true.
  rewrite ! Bool.andb_true_l.
  replace (Int.cmpu Cle Int.zero (Int.repr 255)) with true by reflexivity; simpl.
  rewrite decode_arm32_RSB_I_OP_dst2.
  replace (Int.eq (Int.repr 14) Int.zero) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 14) (Int.repr 2)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 14) (Int.repr 4)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 14) (Int.repr 8)) with false by reflexivity; simpl.
  rewrite Int.eq_true.

  unfold encode_arm32, encode_arm32.
  rewrite bitfield_insert_over_size_zero with (pos := 8%Z)(x := 0%Z); auto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  prove_int.
Qed.


Lemma decode_arm32_EOR_I_OP_LO_11_5:
  forall dst si,
    (decode_arm32
       (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) EOR_I_OP 0 4) 16 16)
       11 5) = Int.repr 30.
Proof.
  intros.
  unfold EOR_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  auto.
Qed.

Lemma decode_arm32_EOR_I_OP_HI_11_5:
  forall dst si,
  (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) EOR_I_OP 0 4) 16
             16) 0 16) 11 5) = Int.repr 30.
Proof.
  intros.
  unfold EOR_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_EOR_I_OP_15_1:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) EOR_I_OP 0 4) 16
             16) 16 16) 15 1) =
        Int.zero.
Proof.
  intros.
  unfold EOR_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 15%Z) (width1 := 1%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  eapply unsigned_bitfield_extract_over_size; eauto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
Qed.

Lemma decode_arm32_EOR_I_OP_5_4:
  forall dst si,
   (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) EOR_I_OP 0 4) 16
             16) 0 16) 5 4) = (Int.repr 4).
Proof.
  intros.
  unfold EOR_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_EOR_I_OP_dst:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) EOR_I_OP 0 4) 16
             16) 16 16) 8 4) =
        Some (ireg_of_breg dst).
Proof.
  intros.
  unfold EOR_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 8%Z) (width := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{ unfold int_of_breg; destruct dst; prove_int. }

  apply int2ireg_int_of_breg_same; auto.
Qed.

Lemma decode_arm32_EOR_I_OP_9_1:
  forall dst si,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) EOR_I_OP 0 4) 16
             16) 0 16) 9 1) =
        Int.zero.
Proof.
  intros.
  unfold EOR_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_EOR_I_OP_4_1:
  forall dst si,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) EOR_I_OP 0 4) 16
             16) 0 16) 4 1) =
        Int.zero.
Proof.
  intros.
  unfold EOR_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_EOR_I_OP_10_1:
  forall dst si,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) EOR_I_OP 0 4) 16
             16) 0 16) 10 1) =
        Int.zero.
Proof.
  intros.
  unfold EOR_I_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_arm32_EOR_I_OP_12_3:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) EOR_I_OP 0 4) 16
             16) 16 16) 12 3) =
        Int.zero.
Proof.
  intros.
  unfold EOR_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 12%Z) (width1 := 3%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  eapply unsigned_bitfield_extract_over_size; eauto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
Qed.

Lemma decode_arm32_EOR_I_OP_0_8:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) EOR_I_OP 0 4) 16
             16) 16 16) 0 8) = si.
Proof.
  intros.
  unfold EOR_I_OP, decode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in H.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 8%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  apply unsigned_bitfield_extract_low_same; auto.
  replace Int.zwordsize with 32%Z by reflexivity; lia.
Qed.

Lemma decode_arm32_EOR_I_OP_dst2:
  forall dst si,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) EOR_I_OP 0 4) 16
             16) 0 16) 0 4) = Some (ireg_of_breg dst).
Proof.
  intros.
  unfold EOR_I_OP, NOP_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; auto.
Qed.

Lemma decode_xor_i:
  forall dst si,
    Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    decode_thumb
      (encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) EOR_I_OP 0 4) 16 16) =
      Some (Peor (ireg_of_breg dst) (ireg_of_breg dst) (SOimm si)).
Proof.
  intros dst si Hcmp.
  unfold decode_thumb.
  rewrite decode_arm32_EOR_I_OP_LO_11_5.
  replace (Int.eq (Int.repr 30) (Int.repr 23)) with false by reflexivity.
  unfold decode_thumb2.
  rewrite decode_arm32_EOR_I_OP_HI_11_5.
  replace (Int.eq (Int.repr 30) (Int.repr 29)) with false by reflexivity.
  rewrite Int.eq_true.
  rewrite decode_arm32_EOR_I_OP_15_1; [| assumption].
  rewrite Int.eq_true.
  rewrite decode_arm32_EOR_I_OP_5_4.
  replace (Int.eq (Int.repr 4) (Int.repr 13)) with false by reflexivity.
  rewrite Bool.andb_false_l.

  rewrite decode_arm32_EOR_I_OP_dst; [| assumption].
  rewrite decode_arm32_EOR_I_OP_9_1.
  replace (Int.eq Int.zero Int.one) with false by reflexivity.
  rewrite Bool.andb_false_l.
  rewrite decode_arm32_EOR_I_OP_4_1.
  rewrite Int.eq_true.
  rewrite Bool.andb_true_l.

  rewrite decode_arm32_EOR_I_OP_10_1.
  rewrite decode_arm32_EOR_I_OP_12_3; [| assumption].
  rewrite decode_arm32_EOR_I_OP_0_8; [| assumption].
  unfold thumb_constant_range_imm12.
  rewrite Int.eq_true, Hcmp.
  rewrite ! Bool.andb_true_l.
  rewrite decode_arm32_EOR_I_OP_dst2.
  replace (Int.eq (Int.repr 4) Int.zero) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 4) (Int.repr 2)) with false by reflexivity; simpl.
  rewrite Int.eq_true.

  unfold encode_arm32, encode_arm32.

  apply int_le_0_255_size_8 in Hcmp.
  rewrite bitfield_insert_over_size_zero with (pos := 8%Z)(x := 8%Z); auto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  rewrite bitfield_insert_over_size_zero with (x := 8%Z); auto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
Qed.

Lemma decode_add_i_11:
  forall si,
  Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true ->
    decode_thumb
      (encode_arm32 (encode_arm32 (Int.repr 11) si 8 4)
         (encode_arm32 (Int.repr 11) ADD_I_OP 0 4) 16 16) = 
    Some (Padd IR11 IR11 (SOimm si)).
Proof.
  intros si Hcmp.
  unfold decode_thumb.
  rewrite decode_arm32_ADD_I_OP_LO_11_5.
  replace (Int.eq (Int.repr 30) (Int.repr 23)) with false by reflexivity.
  unfold decode_thumb2.

  assert (Heq: (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 11) si 8 4) (encode_arm32 (Int.repr 11) ADD_I_OP 0 4) 16 16) 0 16)
       11 5) = Int.repr 30). {
    unfold ADD_I_OP, decode_arm32, encode_arm32.
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    auto.
  }
  rewrite Heq; clear Heq.

  replace (Int.eq (Int.repr 30) (Int.repr 29)) with false by reflexivity.
  rewrite Int.eq_true.

  apply int_le_0_255_size_8 in Hcmp as Hsize.

  assert (Heq: (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 11) si 8 4) (encode_arm32 (Int.repr 11) ADD_I_OP 0 4) 16 16) 16 16)
       15 1) = Int.zero). {
    unfold ADD_I_OP, decode_arm32, encode_arm32.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
    2:{
      apply size_bitfield_insert; try lia.
      prove_int.
    }

    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 15%Z) (width1 := 1%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].

    eapply unsigned_bitfield_extract_over_size; eauto;
      replace Int.zwordsize with 32%Z by reflexivity; try lia.
  }
  rewrite Heq; clear Heq.

  rewrite Int.eq_true.
  assert (Heq: (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 11) si 8 4) (encode_arm32 (Int.repr 11) ADD_I_OP 0 4) 16 16) 0 16)
       5 4) = (Int.repr 8)). {
    unfold ADD_I_OP, decode_arm32, encode_arm32.
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    auto.
  }
  rewrite Heq; clear Heq.

  replace (Int.eq (Int.repr 8) (Int.repr 13)) with false by reflexivity.
  rewrite Bool.andb_false_l.

  assert (Heq: int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 11) si 8 4) (encode_arm32 (Int.repr 11) ADD_I_OP 0 4) 16 16) 16 16)
       8 4) =
        Some IR11). {
    unfold ADD_I_OP, decode_arm32, encode_arm32.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
    2:{
      apply size_bitfield_insert; try lia.
      prove_int.
    }
    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 8%Z) (width := 4%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
    prove_int.
  }
  rewrite Heq; clear Heq.

  assert (Heq: (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 11) si 8 4) (encode_arm32 (Int.repr 11) ADD_I_OP 0 4) 16 16) 0 16)
       9 1) = Int.zero). {
    unfold ADD_I_OP, decode_arm32, encode_arm32.
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    auto.
  }
  rewrite Heq; clear Heq.
  replace (Int.eq Int.zero Int.one) with false by reflexivity.
  rewrite Bool.andb_false_l.

  assert (Heq: (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 11) si 8 4) (encode_arm32 (Int.repr 11) ADD_I_OP 0 4) 16 16) 0 16)
       4 1) = Int.zero). {
    unfold ADD_I_OP, decode_arm32, encode_arm32.
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    auto.
  }
  rewrite Heq; clear Heq.
  rewrite Int.eq_true.
  rewrite Int.eq_true.
  rewrite Bool.andb_true_l.

  assert (Heq: (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 11) si 8 4) (encode_arm32 (Int.repr 11) ADD_I_OP 0 4) 16 16) 0 16)
       10 1) = Int.zero). {
    unfold ADD_I_OP, decode_arm32, encode_arm32.
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    auto.
  }
  rewrite Heq; clear Heq.

  assert (Heq: (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 11) si 8 4) (encode_arm32 (Int.repr 11) ADD_I_OP 0 4) 16 16) 16 16)
       12 3) = Int.zero). {
    unfold ADD_I_OP, decode_arm32, encode_arm32.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
    2:{
      apply size_bitfield_insert; try lia.
      prove_int.
    }
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 12%Z) (width1 := 3%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    eapply unsigned_bitfield_extract_over_size; eauto;
      replace Int.zwordsize with 32%Z by reflexivity; try lia.
  }
  rewrite Heq; clear Heq.

  assert (Heq: (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 11) si 8 4) (encode_arm32 (Int.repr 11) ADD_I_OP 0 4) 16 16) 16 16)
       0 8) = si). {
    unfold ADD_I_OP, decode_arm32, encode_arm32.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
    2:{
      apply size_bitfield_insert; try lia.
      prove_int.
    }
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 8%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    apply unsigned_bitfield_extract_low_same; auto.
    replace Int.zwordsize with 32%Z by reflexivity; lia.
  }
  rewrite Heq; clear Heq.
  unfold thumb_constant_range_imm12.
  rewrite Int.eq_true, Hcmp.
  rewrite ! Bool.andb_true_l.

  assert (Heq: int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 11) si 8 4) (encode_arm32 (Int.repr 11) ADD_I_OP 0 4) 16 16) 0 16)
       0 4) = Some IR11). {
    unfold ADD_I_OP, NOP_OP, decode_arm32, encode_arm32.
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    auto.
  }
  rewrite Heq; clear Heq.
  replace (Int.eq (Int.repr 8) Int.zero) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 8) (Int.repr 2)) with false by reflexivity; simpl.

  unfold encode_arm32, encode_arm32.

  rewrite bitfield_insert_over_size_zero with (pos := 8%Z)(x := 8%Z); auto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  rewrite bitfield_insert_over_size_zero with (x := 8%Z); auto;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
Qed.