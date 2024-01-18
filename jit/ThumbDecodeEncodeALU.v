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

Lemma decode_arm32_ADD_R_OP_11_5:
  forall dst src,
  (decode_arm32
       (encode_arm32
          (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
             (encode_arm32 (int_of_ireg src)
                (encode_arm32
                   (if Int.lt (int_of_breg dst) (Int.repr 8)
                    then int_of_breg dst
                    else Int.sub (int_of_breg dst) (Int.repr 8)) ADD_R_OP 0 3) 3 4) 7 1) NOP_OP
          16 16) 11 5) = Int.repr 23.
Proof.
  intros.
  unfold NOP_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  auto.
Qed.

Lemma decode_arm32_ADD_R_OP_NOP_OP:
  forall dst src,
  (decode_arm32
       (encode_arm32
          (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
             (encode_arm32 (int_of_ireg src)
                (encode_arm32
                   (if Int.lt (int_of_breg dst) (Int.repr 8)
                    then int_of_breg dst
                    else Int.sub (int_of_breg dst) (Int.repr 8)) ADD_R_OP 0 3) 3 4) 7 1) NOP_OP
          16 16) 0 16) = NOP_OP.
Proof.
  intros.
  unfold NOP_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  auto.
Qed.

Lemma decode_arm32_ADD_R_OP_10_6:
  forall dst src,
  (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
                (encode_arm32 (int_of_ireg src)
                   (encode_arm32
                      (if Int.lt (int_of_breg dst) (Int.repr 8)
                       then int_of_breg dst
                       else Int.sub (int_of_breg dst) (Int.repr 8)) ADD_R_OP 0 3) 3 4) 7 1)
             NOP_OP 16 16) 16 16) 10 6) =
      Int.repr 17.
Proof.
  intros.
  unfold ADD_R_OP, decode_arm32, encode_arm32.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + apply size_bitfield_insert; try lia.
        * prove_int.
        * unfold int_of_breg; destruct dst; prove_int.
      + unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 7%Z) (width0 := 1%Z) (pos1 := 10%Z) (width1 := 6%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 3%Z) (width0 := 4%Z) (pos1 := 10%Z) (width1 := 6%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 0%Z) (width0 := 3%Z) (pos1 := 10%Z) (width1 := 6%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  auto.
Qed.

Lemma decode_arm32_ADD_R_OP_dst_4:
  forall dst src,
   (decode_arm32
        (decode_arm32
           (encode_arm32
              (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
                 (encode_arm32 (int_of_ireg src)
                    (encode_arm32
                       (if Int.lt (int_of_breg dst) (Int.repr 8)
                        then int_of_breg dst
                        else Int.sub (int_of_breg dst) (Int.repr 8)) ADD_R_OP 0 3) 3 4) 7 1)
              NOP_OP 16 16) 16 16) 7 1) =
      if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one.
Proof.
  intros.
  unfold ADD_R_OP, NOP_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + apply size_bitfield_insert; try lia.
        * prove_int.
        * unfold int_of_breg; destruct dst; prove_int.
      + unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same with
    (pos := 7%Z) (width := 1%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  instantiate (1 := Int.bitfield_insert 7 1 Int.zero
    (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)).
  destruct dst; repeat int_true_false.
Qed.

Lemma decode_arm32_ADD_R_OP_dst_0_3:
  forall dst src,
    (decode_arm32
        (decode_arm32
           (encode_arm32
              (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
                 (encode_arm32 (int_of_ireg src)
                    (encode_arm32
                       (if Int.lt (int_of_breg dst) (Int.repr 8)
                        then int_of_breg dst
                        else Int.sub (int_of_breg dst) (Int.repr 8)) ADD_R_OP 0 3) 3 4) 7 1)
              NOP_OP 16 16) 16 16) 0 3) =
      if Int.lt (int_of_breg dst) (Int.repr 8)
        then int_of_breg dst
        else Int.sub (int_of_breg dst) (Int.repr 8).
Proof.
  intros.
  unfold ADD_R_OP, NOP_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + apply size_bitfield_insert; try lia.
        * prove_int.
        * unfold int_of_breg; destruct dst; prove_int.
      + unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 7%Z) (width0 := 1%Z) (pos1 := 0%Z) (width1 := 3%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 3%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 3%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite bitfield_insert_unsigned_bitfield_extract_same with
    (pos := 0%Z) (width := 3%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  instantiate (1 := Int.bitfield_insert 0 3 Int.zero
    (if Int.lt (int_of_breg dst) (Int.repr 8) then int_of_breg dst else Int.sub (int_of_breg dst) (Int.repr 8))).
  destruct dst; repeat int_true_false.
Qed.

Lemma decode_arm32_ADD_R_OP_dst:
  forall dst src,
int2ireg
    (encode_arm32
       (decode_arm32
          (decode_arm32
             (encode_arm32
                (encode_arm32
                   (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
                   (encode_arm32 (int_of_ireg src)
                      (encode_arm32
                         (if Int.lt (int_of_breg dst) (Int.repr 8)
                          then int_of_breg dst
                          else Int.sub (int_of_breg dst) (Int.repr 8)) ADD_R_OP 0 3) 3 4) 7 1)
                NOP_OP 16 16) 16 16) 7 1)
       (decode_arm32
          (decode_arm32
             (encode_arm32
                (encode_arm32
                   (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
                   (encode_arm32 (int_of_ireg src)
                      (encode_arm32
                         (if Int.lt (int_of_breg dst) (Int.repr 8)
                          then int_of_breg dst
                          else Int.sub (int_of_breg dst) (Int.repr 8)) ADD_R_OP 0 3) 3 4) 7 1)
                NOP_OP 16 16) 16 16) 0 3) 3 1)  = Some (ireg_of_breg dst).
Proof.
  intros.
  rewrite decode_arm32_ADD_R_OP_dst_4.
  rewrite decode_arm32_ADD_R_OP_dst_0_3.
  unfold encode_arm32.

  destruct dst; unfold int_of_breg; simpl; prove_int_bit;
  unfold int2ireg; auto.
Qed.

Lemma decode_arm32_ADD_R_OP_src:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
                (encode_arm32 (int_of_ireg src)
                   (encode_arm32
                      (if Int.lt (int_of_breg dst) (Int.repr 8)
                       then int_of_breg dst
                       else Int.sub (int_of_breg dst) (Int.repr 8)) ADD_R_OP 0 3) 3 4) 7 1)
             NOP_OP 16 16) 16 16) 3 4) = Some src.
Proof.
  intros.
  unfold ADD_R_OP, NOP_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + apply size_bitfield_insert; try lia.
        * prove_int.
        * unfold int_of_breg; destruct dst; prove_int.
      + unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 7%Z) (width0 := 1%Z) (pos1 := 3%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  simpl.
  erewrite bitfield_insert_unsigned_bitfield_extract_same with
    (pos := 3%Z) (width := 4%Z) (p := Int.bitfield_insert 3 4 Int.zero (int_of_ireg src))
    (i := (Int.bitfield_insert 0 3 (Int.repr 17408)
           (if Int.lt (int_of_breg dst) (Int.repr 8)
            then int_of_breg dst
            else Int.sub (int_of_breg dst) (Int.repr 8))));
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  - destruct src; repeat int_true_false.
  - assert (Heq: (Int.unsigned_bitfield_extract 3 4 (Int.bitfield_insert 3 4 Int.zero
      (int_of_ireg src))) = (int_of_ireg src)).
    + erewrite bitfield_insert_unsigned_bitfield_extract_same with
      (pos := 3%Z) (width := 4%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.

      instantiate (1 := Int.bitfield_insert 3 4 Int.zero
        (int_of_ireg src)).
      destruct src; repeat int_true_false.
    + rewrite Heq.
      f_equal.
Qed.

Lemma decode_arm32_ADD_R_OP_dst_8_2:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
                (encode_arm32 (int_of_ireg src)
                   (encode_arm32
                      (if Int.lt (int_of_breg dst) (Int.repr 8)
                       then int_of_breg dst
                       else Int.sub (int_of_breg dst) (Int.repr 8)) ADD_R_OP 0 3) 3 4) 7 1)
             NOP_OP 16 16) 16 16) 8 2) = Int.zero.
Proof.
  intros.
  unfold ADD_R_OP, NOP_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + apply size_bitfield_insert; try lia.
        * prove_int.
        * unfold int_of_breg; destruct dst; prove_int.
      + unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 7%Z) (width0 := 1%Z) (pos1 := 8%Z) (width1 := 2%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 3%Z) (width0 := 4%Z) (pos1 := 8%Z) (width1 := 2%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 0%Z) (width0 := 3%Z) (pos1 := 8%Z) (width1 := 2%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  auto.
Qed.

Lemma decode_add_r:
  forall dst src,
    decode_thumb
      (encode_arm32
         (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
            (encode_arm32 (int_of_ireg src)
               (encode_arm32
                  (if Int.lt (int_of_breg dst) (Int.repr 8)
                   then int_of_breg dst
                   else Int.sub (int_of_breg dst) (Int.repr 8)) ADD_R_OP 0 3) 3 4) 7 1) NOP_OP 16
         16) = Some (Padd (ireg_of_breg dst) (ireg_of_breg dst)
                (SOreg src)).
Proof.
  intros.
  unfold decode_thumb.
  rewrite decode_arm32_ADD_R_OP_11_5.
  rewrite Int.eq_true.
  rewrite decode_arm32_ADD_R_OP_NOP_OP.
  rewrite Int.eq_true.
  unfold decode_thumb1.
  rewrite decode_arm32_ADD_R_OP_10_6.
  rewrite Int.eq_true.

  rewrite decode_arm32_ADD_R_OP_dst.
  rewrite decode_arm32_ADD_R_OP_src.
  rewrite decode_arm32_ADD_R_OP_dst_8_2.
  rewrite Int.eq_true.
  f_equal.
Qed.

Lemma decode_arm32_SUB_R_OP_HI_11_5:
  forall dst src,
  (decode_arm32
       (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
          (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16) 11 5) = Int.repr 29.
Proof.
  intros.
  unfold SUB_R_OP, decode_arm32, encode_arm32.
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

Lemma decode_arm32_SUB_R_OP_LO_11_5:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16) 0 16) 11 5) =
    (Int.repr 29).
Proof.
  intros.
  unfold SUB_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; auto.
Qed.

Lemma decode_arm32_SUB_R_OP_9_2:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16) 0 16) 9 2) = Int.one.
Proof.
  intros.
  unfold SUB_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; auto.
Qed.

Lemma decode_arm32_SUB_R_OP_4_1:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16) 0 16) 4 1) = Int.zero.
Proof.
  intros.
  unfold SUB_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; auto.
Qed.

Lemma decode_arm32_SUB_R_OP_12_4:
  forall dst src,
    (decode_arm32
        (decode_arm32
           (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
              (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16) 16 16) 12 4) = Int.zero.
Proof.
  intros.
  unfold SUB_R_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 12%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct src; simpl; auto.
Qed.

Lemma decode_arm32_SUB_R_OP_4_4:
  forall dst src,
    (decode_arm32
        (decode_arm32
           (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
              (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16) 16 16) 4 4) = Int.zero.
Proof.
  intros.
  unfold SUB_R_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 4%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct src; simpl; auto.
Qed.

Lemma decode_arm32_SUB_R_OP_dst:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16) 0 16) 0 4) = Some (ireg_of_breg dst).
Proof.
  intros.
  unfold SUB_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  unfold int2ireg, int_of_breg, ireg_of_breg;
  destruct dst; repeat int_true_false; f_equal.
Qed.

Lemma decode_arm32_SUB_R_OP_dst2:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16) 16 16) 8 4) = Some (ireg_of_breg dst).
Proof.
  intros.
  unfold SUB_R_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 8%Z) (width := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{ unfold int_of_breg; destruct dst; prove_int. }

  apply int2ireg_int_of_breg_same.
Qed.

Lemma decode_arm32_SUB_R_OP_src:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16) 16 16) 0 4) = Some src.
Proof.
  intros.
  unfold SUB_R_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  rewrite unsigned_bitfield_extract_low_same.
  - rewrite int2ireg_int_of_ireg_same. reflexivity.
  - replace Int.zwordsize with 32%Z by reflexivity; lia.
  - destruct src; unfold int_of_ireg; simpl; prove_int.
Qed.

Lemma decode_arm32_SUB_R_OP_5_4:
  forall dst src,
    (decode_arm32
          (decode_arm32
             (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
                (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16) 0 16) 5 4) =
       (Int.repr 13).
Proof.
  intros.
  unfold SUB_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; repeat int_true_false; f_equal.
Qed.

Lemma decode_sub_r:
  forall dst src,
    decode_thumb
      (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
         (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16) =
      Some (Psub (ireg_of_breg dst) (ireg_of_breg dst)
                (SOreg src)).
Proof.
  intros.
  unfold decode_thumb.
  rewrite decode_arm32_SUB_R_OP_HI_11_5.
  replace (Int.eq (Int.repr 29) (Int.repr 23)) with false by reflexivity; simpl.
  unfold decode_thumb2.
  rewrite decode_arm32_SUB_R_OP_LO_11_5.
  rewrite Int.eq_true.

  rewrite decode_arm32_SUB_R_OP_9_2.
  rewrite Int.eq_true.
  rewrite decode_arm32_SUB_R_OP_4_1.
  rewrite Int.eq_true.
  rewrite decode_arm32_SUB_R_OP_12_4.
  rewrite Int.eq_true.
  rewrite decode_arm32_SUB_R_OP_4_4.
  rewrite Int.eq_true.
  simpl.
  rewrite decode_arm32_SUB_R_OP_dst.
  rewrite decode_arm32_SUB_R_OP_dst2.
  rewrite decode_arm32_SUB_R_OP_src.
  rewrite decode_arm32_SUB_R_OP_5_4.
  replace (Int.eq (Int.repr 13) Int.zero) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 13) (Int.repr 2)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 13) (Int.repr 4)) with false by reflexivity; simpl.
  rewrite Int.eq_true.
  f_equal.
Qed.

Lemma decode_arm32_MUL_OP_HI_11_5:
  forall dst src,
  (decode_arm32
       (encode_arm32
          (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12 4)
          (encode_arm32 (int_of_breg dst) MUL_OP 0 4) 16 16) 11 5) = Int.repr 31.
Proof.
  intros.
  unfold MUL_OP, decode_arm32, encode_arm32.
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

Lemma decode_arm32_MUL_OP_LO_11_5:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12
                4) (encode_arm32 (int_of_breg dst) MUL_OP 0 4) 16 16) 0 16) 11 5)  =
    (Int.repr 31).
Proof.
  intros.
  unfold MUL_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; auto.
Qed.

Lemma decode_arm32_MUL_OP_9_2:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12
                4) (encode_arm32 (int_of_breg dst) MUL_OP 0 4) 16 16) 0 16) 9 2) = Int.one.
Proof.
  intros.
  unfold MUL_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; auto.
Qed.

Lemma decode_arm32_MUL_OP_dst:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12
                4) (encode_arm32 (int_of_breg dst) MUL_OP 0 4) 16 16) 0 16) 0 4) = Some (ireg_of_breg dst).
Proof.
  intros.
  unfold MUL_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  unfold int2ireg, int_of_breg, ireg_of_breg;
  destruct dst; repeat int_true_false; f_equal.
Qed.

Lemma decode_arm32_MUL_OP_src:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12
                4) (encode_arm32 (int_of_breg dst) MUL_OP 0 4) 16 16) 16 16) 0 4) = Some src.
Proof.
  intros.
  unfold MUL_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
      + unfold int_of_breg; destruct dst; prove_int.
    - prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 12%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  rewrite unsigned_bitfield_extract_low_same.
  - rewrite int2ireg_int_of_ireg_same. reflexivity.
  - replace Int.zwordsize with 32%Z by reflexivity; lia.
  - destruct src; unfold int_of_ireg; simpl; prove_int.
Qed.

Lemma decode_arm32_MUL_OP_dst2:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12
                4) (encode_arm32 (int_of_breg dst) MUL_OP 0 4) 16 16) 16 16) 8 4) = Some (ireg_of_breg dst).
Proof.
  intros.
  unfold MUL_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
      + unfold int_of_breg; destruct dst; prove_int.
    - prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 12%Z) (width0 := 4%Z) (pos1 := 8%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 8%Z) (width := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{ unfold int_of_breg; destruct dst; prove_int. }

  apply int2ireg_int_of_breg_same.
Qed.

Lemma decode_arm32_MUL_OP_12_4:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12
                4) (encode_arm32 (int_of_breg dst) MUL_OP 0 4) 16 16) 16 16) 12 4) = Int.repr 15.
Proof.
  intros.
  unfold MUL_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
      + unfold int_of_breg; destruct dst; prove_int.
    - prove_int.
  }
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 12%Z) (width := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.

  prove_int.
Qed.

Lemma decode_arm32_MUL_OP_4_4:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12
                4) (encode_arm32 (int_of_breg dst) MUL_OP 0 4) 16 16) 16 16) 4 4) = Int.zero.
Proof.
  intros.
  unfold MUL_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
      + unfold int_of_breg; destruct dst; prove_int.
    - prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 12%Z) (width0 := 4%Z) (pos1 := 4%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 4%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct src; simpl; auto.
Qed.

Lemma decode_arm32_MUL_OP_4_1:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12
                4) (encode_arm32 (int_of_breg dst) MUL_OP 0 4) 16 16) 0 16) 4 1) = Int.zero.
Proof.
  intros.
  unfold MUL_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; auto.
Qed.

Lemma decode_arm32_MUL_OP_5_4:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12
                4) (encode_arm32 (int_of_breg dst) MUL_OP 0 4) 16 16) 0 16) 5 4) =
       (Int.repr 8).
Proof.
  intros.
  unfold MUL_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; repeat int_true_false; f_equal.
Qed.

Lemma decode_mul_r:
  forall dst src,
    decode_thumb
      (encode_arm32
         (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12 4)
         (encode_arm32 (int_of_breg dst) MUL_OP 0 4) 16 16) =
      Some (Pmul (ireg_of_breg dst) (ireg_of_breg dst) src).
Proof.
  intros.
  unfold decode_thumb.
  rewrite decode_arm32_MUL_OP_HI_11_5.
  replace (Int.eq (Int.repr 31) (Int.repr 23)) with false by reflexivity; simpl.
  unfold decode_thumb2.
  rewrite decode_arm32_MUL_OP_LO_11_5.
  replace (Int.eq (Int.repr 31) (Int.repr 29)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 30)) with false by reflexivity; simpl.
  rewrite Int.eq_true.

  rewrite decode_arm32_MUL_OP_9_2.
  replace (Int.eq Int.one Int.zero) with false by reflexivity; simpl.
  rewrite Int.eq_true.
  rewrite decode_arm32_MUL_OP_dst.
  rewrite decode_arm32_MUL_OP_src.
  rewrite decode_arm32_MUL_OP_dst2.
  rewrite decode_arm32_MUL_OP_12_4.
  rewrite Int.eq_true.
  rewrite decode_arm32_MUL_OP_4_4.
  rewrite Int.eq_true.
  rewrite decode_arm32_MUL_OP_4_1.
  rewrite Int.eq_true.
  rewrite decode_arm32_MUL_OP_5_4.
  replace (Int.eq (Int.repr 8) Int.zero) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 8) Int.one) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 8) (Int.repr 2)) with false by reflexivity; simpl.
  rewrite Int.eq_true.
  f_equal.
Qed.

Lemma decode_arm32_ORR_R_OP_HI_11_5:
  forall dst src,
  (decode_arm32
       (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
          (encode_arm32 (int_of_breg dst) ORR_R_OP 0 4) 16 16) 11 5) = Int.repr 29.
Proof.
  intros.
  unfold ORR_R_OP, decode_arm32, encode_arm32.
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

Lemma decode_arm32_ORR_R_OP_LO_11_5:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) ORR_R_OP 0 4) 16 16) 0 16) 11 5) =
    (Int.repr 29).
Proof.
  intros.
  unfold ORR_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; auto.
Qed.

Lemma decode_arm32_ORR_R_OP_9_2:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) ORR_R_OP 0 4) 16 16) 0 16) 9 2) = Int.one.
Proof.
  intros.
  unfold ORR_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; auto.
Qed.

Lemma decode_arm32_ORR_R_OP_4_1:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) ORR_R_OP 0 4) 16 16) 0 16) 4 1) = Int.zero.
Proof.
  intros.
  unfold ORR_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; auto.
Qed.

Lemma decode_arm32_ORR_R_OP_12_4:
  forall dst src,
    (decode_arm32
        (decode_arm32
           (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
              (encode_arm32 (int_of_breg dst) ORR_R_OP 0 4) 16 16) 16 16) 12 4) = Int.zero.
Proof.
  intros.
  unfold ORR_R_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 12%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct src; simpl; auto.
Qed.

Lemma decode_arm32_ORR_R_OP_4_4:
  forall dst src,
    (decode_arm32
        (decode_arm32
           (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
              (encode_arm32 (int_of_breg dst) ORR_R_OP 0 4) 16 16) 16 16) 4 4) = Int.zero.
Proof.
  intros.
  unfold ORR_R_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 4%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct src; simpl; auto.
Qed.

Lemma decode_arm32_ORR_R_OP_dst:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) ORR_R_OP 0 4) 16 16) 0 16) 0 4) = Some (ireg_of_breg dst).
Proof.
  intros.
  unfold ORR_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  unfold int2ireg, int_of_breg, ireg_of_breg;
  destruct dst; repeat int_true_false; f_equal.
Qed.

Lemma decode_arm32_ORR_R_OP_dst2:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) ORR_R_OP 0 4) 16 16) 16 16) 8 4) = Some (ireg_of_breg dst).
Proof.
  intros.
  unfold ORR_R_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 8%Z) (width := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{ unfold int_of_breg; destruct dst; prove_int. }

  apply int2ireg_int_of_breg_same.
Qed.

Lemma decode_arm32_ORR_R_OP_src:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) ORR_R_OP 0 4) 16 16) 16 16) 0 4) = Some src.
Proof.
  intros.
  unfold ORR_R_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  rewrite unsigned_bitfield_extract_low_same.
  - rewrite int2ireg_int_of_ireg_same. reflexivity.
  - replace Int.zwordsize with 32%Z by reflexivity; lia.
  - destruct src; unfold int_of_ireg; simpl; prove_int.
Qed.

Lemma decode_arm32_ORR_R_OP_5_4:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) ORR_R_OP 0 4) 16 16) 0 16) 5 4) =
       (Int.repr 2).
Proof.
  intros.
  unfold ORR_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; repeat int_true_false; f_equal.
Qed.

Lemma decode_orr_r:
  forall dst src,
    decode_thumb
      (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
         (encode_arm32 (int_of_breg dst) ORR_R_OP 0 4) 16 16) =
      Some (Porr (ireg_of_breg dst) (ireg_of_breg dst)
                (SOreg src)).
Proof.
  intros.
  unfold decode_thumb.
  rewrite decode_arm32_ORR_R_OP_HI_11_5.
  replace (Int.eq (Int.repr 29) (Int.repr 23)) with false by reflexivity; simpl.
  unfold decode_thumb2.
  rewrite decode_arm32_ORR_R_OP_LO_11_5.
  rewrite Int.eq_true.

  rewrite decode_arm32_ORR_R_OP_9_2.
  rewrite Int.eq_true.
  rewrite decode_arm32_ORR_R_OP_4_1.
  rewrite Int.eq_true.
  rewrite decode_arm32_ORR_R_OP_12_4.
  rewrite Int.eq_true.
  rewrite decode_arm32_ORR_R_OP_4_4.
  rewrite Int.eq_true.
  simpl.
  rewrite decode_arm32_ORR_R_OP_dst.
  rewrite decode_arm32_ORR_R_OP_dst2.
  rewrite decode_arm32_ORR_R_OP_src.
  rewrite decode_arm32_ORR_R_OP_5_4.
  replace (Int.eq (Int.repr 2) Int.zero) with false by reflexivity; simpl.
  rewrite Int.eq_true.
  f_equal.
Qed.

Lemma decode_arm32_AND_R_OP_HI_11_5:
  forall dst src,
  (decode_arm32
       (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
          (encode_arm32 (int_of_breg dst) AND_R_OP 0 4) 16 16) 11 5) = Int.repr 29.
Proof.
  intros.
  unfold AND_R_OP, decode_arm32, encode_arm32.
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

Lemma decode_arm32_AND_R_OP_LO_11_5:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) AND_R_OP 0 4) 16 16) 0 16) 11 5) =
    (Int.repr 29).
Proof.
  intros.
  unfold AND_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; auto.
Qed.

Lemma decode_arm32_AND_R_OP_9_2:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) AND_R_OP 0 4) 16 16) 0 16) 9 2) = Int.one.
Proof.
  intros.
  unfold AND_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; auto.
Qed.

Lemma decode_arm32_AND_R_OP_4_1:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) AND_R_OP 0 4) 16 16) 0 16) 4 1) = Int.zero.
Proof.
  intros.
  unfold AND_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; auto.
Qed.

Lemma decode_arm32_AND_R_OP_12_4:
  forall dst src,
    (decode_arm32
        (decode_arm32
           (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
              (encode_arm32 (int_of_breg dst) AND_R_OP 0 4) 16 16) 16 16) 12 4) = Int.zero.
Proof.
  intros.
  unfold AND_R_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 12%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct src; simpl; auto.
Qed.

Lemma decode_arm32_AND_R_OP_4_4:
  forall dst src,
    (decode_arm32
        (decode_arm32
           (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
              (encode_arm32 (int_of_breg dst) AND_R_OP 0 4) 16 16) 16 16) 4 4) = Int.zero.
Proof.
  intros.
  unfold AND_R_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 4%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct src; simpl; auto.
Qed.

Lemma decode_arm32_AND_R_OP_dst:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) AND_R_OP 0 4) 16 16) 0 16) 0 4) = Some (ireg_of_breg dst).
Proof.
  intros.
  unfold AND_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  unfold int2ireg, int_of_breg, ireg_of_breg;
  destruct dst; repeat int_true_false; f_equal.
Qed.

Lemma decode_arm32_AND_R_OP_dst2:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) AND_R_OP 0 4) 16 16) 16 16) 8 4) = Some (ireg_of_breg dst).
Proof.
  intros.
  unfold AND_R_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 8%Z) (width := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{ unfold int_of_breg; destruct dst; prove_int. }

  apply int2ireg_int_of_breg_same.
Qed.

Lemma decode_arm32_AND_R_OP_src:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) AND_R_OP 0 4) 16 16) 16 16) 0 4) = Some src.
Proof.
  intros.
  unfold AND_R_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  rewrite unsigned_bitfield_extract_low_same.
  - rewrite int2ireg_int_of_ireg_same. reflexivity.
  - replace Int.zwordsize with 32%Z by reflexivity; lia.
  - destruct src; unfold int_of_ireg; simpl; prove_int.
Qed.

Lemma decode_arm32_AND_R_OP_5_4:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) AND_R_OP 0 4) 16 16) 0 16) 5 4) =
       Int.zero.
Proof.
  intros.
  unfold AND_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; repeat int_true_false; f_equal.
Qed.

Lemma decode_and_r:
  forall dst src,
    decode_thumb
      (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
         (encode_arm32 (int_of_breg dst) AND_R_OP 0 4) 16 16) =
      Some (Pand (ireg_of_breg dst) (ireg_of_breg dst)
                (SOreg src)).
Proof.
  intros.
  unfold decode_thumb.
  rewrite decode_arm32_AND_R_OP_HI_11_5.
  replace (Int.eq (Int.repr 29) (Int.repr 23)) with false by reflexivity; simpl.
  unfold decode_thumb2.
  rewrite decode_arm32_AND_R_OP_LO_11_5.
  rewrite Int.eq_true.

  rewrite decode_arm32_AND_R_OP_9_2.
  rewrite Int.eq_true.
  rewrite decode_arm32_AND_R_OP_4_1.
  rewrite Int.eq_true.
  rewrite decode_arm32_AND_R_OP_12_4.
  rewrite Int.eq_true.
  rewrite decode_arm32_AND_R_OP_4_4.
  rewrite Int.eq_true.
  simpl.
  rewrite decode_arm32_AND_R_OP_dst.
  rewrite decode_arm32_AND_R_OP_dst2.
  rewrite decode_arm32_AND_R_OP_src.
  rewrite decode_arm32_AND_R_OP_5_4.
  rewrite Int.eq_true.
  f_equal.
Qed.

Lemma decode_arm32_EOR_R_OP_HI_11_5:
  forall dst src,
  (decode_arm32
       (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
          (encode_arm32 (int_of_breg dst) EOR_R_OP 0 4) 16 16) 11 5) = Int.repr 29.
Proof.
  intros.
  unfold EOR_R_OP, decode_arm32, encode_arm32.
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

Lemma decode_arm32_EOR_R_OP_LO_11_5:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) EOR_R_OP 0 4) 16 16) 0 16) 11 5) =
    (Int.repr 29).
Proof.
  intros.
  unfold EOR_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; auto.
Qed.

Lemma decode_arm32_EOR_R_OP_9_2:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) EOR_R_OP 0 4) 16 16) 0 16) 9 2) = Int.one.
Proof.
  intros.
  unfold EOR_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; auto.
Qed.

Lemma decode_arm32_EOR_R_OP_4_1:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) EOR_R_OP 0 4) 16 16) 0 16) 4 1) = Int.zero.
Proof.
  intros.
  unfold EOR_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; auto.
Qed.

Lemma decode_arm32_EOR_R_OP_12_4:
  forall dst src,
    (decode_arm32
        (decode_arm32
           (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
              (encode_arm32 (int_of_breg dst) EOR_R_OP 0 4) 16 16) 16 16) 12 4) = Int.zero.
Proof.
  intros.
  unfold EOR_R_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 12%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct src; simpl; auto.
Qed.

Lemma decode_arm32_EOR_R_OP_4_4:
  forall dst src,
    (decode_arm32
        (decode_arm32
           (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
              (encode_arm32 (int_of_breg dst) EOR_R_OP 0 4) 16 16) 16 16) 4 4) = Int.zero.
Proof.
  intros.
  unfold EOR_R_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 4%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct src; simpl; auto.
Qed.

Lemma decode_arm32_EOR_R_OP_dst:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) EOR_R_OP 0 4) 16 16) 0 16) 0 4) = Some (ireg_of_breg dst).
Proof.
  intros.
  unfold EOR_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  unfold int2ireg, int_of_breg, ireg_of_breg;
  destruct dst; repeat int_true_false; f_equal.
Qed.

Lemma decode_arm32_EOR_R_OP_dst2:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) EOR_R_OP 0 4) 16 16) 16 16) 8 4) = Some (ireg_of_breg dst).
Proof.
  intros.
  unfold EOR_R_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 8%Z) (width := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{ unfold int_of_breg; destruct dst; prove_int. }

  apply int2ireg_int_of_breg_same.
Qed.

Lemma decode_arm32_EOR_R_OP_src:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) EOR_R_OP 0 4) 16 16) 16 16) 0 4) = Some src.
Proof.
  intros.
  unfold EOR_R_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  rewrite unsigned_bitfield_extract_low_same.
  - rewrite int2ireg_int_of_ireg_same. reflexivity.
  - replace Int.zwordsize with 32%Z by reflexivity; lia.
  - destruct src; unfold int_of_ireg; simpl; prove_int.
Qed.

Lemma decode_arm32_EOR_R_OP_5_4:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
             (encode_arm32 (int_of_breg dst) EOR_R_OP 0 4) 16 16) 0 16) 5 4) =
       Int.repr 4.
Proof.
  intros.
  unfold EOR_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; repeat int_true_false; f_equal.
Qed.

Lemma decode_xor_r:
  forall dst src,
    decode_thumb
      (encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4)
         (encode_arm32 (int_of_breg dst) EOR_R_OP 0 4) 16 16) =
      Some (Peor (ireg_of_breg dst) (ireg_of_breg dst)
                (SOreg src)).
Proof.
  intros.
  unfold decode_thumb.
  rewrite decode_arm32_EOR_R_OP_HI_11_5.
  replace (Int.eq (Int.repr 29) (Int.repr 23)) with false by reflexivity; simpl.
  unfold decode_thumb2.
  rewrite decode_arm32_EOR_R_OP_LO_11_5.
  rewrite Int.eq_true.

  rewrite decode_arm32_EOR_R_OP_9_2.
  rewrite Int.eq_true.
  rewrite decode_arm32_EOR_R_OP_4_1.
  rewrite Int.eq_true.
  rewrite decode_arm32_EOR_R_OP_12_4.
  rewrite Int.eq_true.
  rewrite decode_arm32_EOR_R_OP_4_4.
  rewrite Int.eq_true.
  simpl.
  rewrite decode_arm32_EOR_R_OP_dst.
  rewrite decode_arm32_EOR_R_OP_dst2.
  rewrite decode_arm32_EOR_R_OP_src.
  rewrite decode_arm32_EOR_R_OP_5_4.
  replace (Int.eq (Int.repr 4) Int.zero) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 4) (Int.repr 2)) with false by reflexivity; simpl.
  rewrite Int.eq_true.
  f_equal.
Qed.


Lemma decode_arm32_MOV_R_OP_11_5:
  forall x y z,
  (decode_arm32
       (encode_arm32
          (encode_arm32 x
             (encode_arm32 y
                (encode_arm32
                   z MOV_R_OP 0 3) 3 4) 7 1) NOP_OP
          16 16) 11 5) = Int.repr 23.
Proof.
  intros.
  unfold NOP_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  auto.
Qed.

Lemma decode_arm32_MOV_R_OP_NOP_OP:
  forall x y z,
  (decode_arm32
       (encode_arm32
          (encode_arm32 x
             (encode_arm32 y
                (encode_arm32
                   z MOV_R_OP 0 3) 3 4) 7 1) NOP_OP
          16 16) 0 16) = NOP_OP.
Proof.
  intros.
  unfold NOP_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  auto.
Qed.

Lemma decode_arm32_MOV_R_OP_10_6:
  forall dst src,
  (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
                (encode_arm32 (int_of_ireg src)
                   (encode_arm32
                      (if Int.lt (int_of_breg dst) (Int.repr 8)
                       then int_of_breg dst
                       else Int.sub (int_of_breg dst) (Int.repr 8)) MOV_R_OP 0 3) 3 4) 7 1)
             NOP_OP 16 16) 16 16) 10 6) =
      Int.repr 17.
Proof.
  intros.
  unfold MOV_R_OP, decode_arm32, encode_arm32.

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + apply size_bitfield_insert; try lia.
        * prove_int.
        * unfold int_of_breg; destruct dst; prove_int.
      + unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 7%Z) (width0 := 1%Z) (pos1 := 10%Z) (width1 := 6%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 3%Z) (width0 := 4%Z) (pos1 := 10%Z) (width1 := 6%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 0%Z) (width0 := 3%Z) (pos1 := 10%Z) (width1 := 6%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  auto.
Qed.

Lemma decode_arm32_MOV_R_OP_dst_4:
  forall dst src,
   (decode_arm32
        (decode_arm32
           (encode_arm32
              (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
                 (encode_arm32 (int_of_ireg src)
                    (encode_arm32
                       (if Int.lt (int_of_breg dst) (Int.repr 8)
                        then int_of_breg dst
                        else Int.sub (int_of_breg dst) (Int.repr 8)) MOV_R_OP 0 3) 3 4) 7 1)
              NOP_OP 16 16) 16 16) 7 1) =
      if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one.
Proof.
  intros.
  unfold MOV_R_OP, NOP_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + apply size_bitfield_insert; try lia.
        * prove_int.
        * unfold int_of_breg; destruct dst; prove_int.
      + unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same with
    (pos := 7%Z) (width := 1%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  instantiate (1 := Int.bitfield_insert 7 1 Int.zero
    (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)).
  destruct dst; repeat int_true_false.
Qed.

Lemma decode_arm32_MOV_R_OP_dst_0_3:
  forall dst src,
    (decode_arm32
        (decode_arm32
           (encode_arm32
              (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
                 (encode_arm32 (int_of_ireg src)
                    (encode_arm32
                       (if Int.lt (int_of_breg dst) (Int.repr 8)
                        then int_of_breg dst
                        else Int.sub (int_of_breg dst) (Int.repr 8)) MOV_R_OP 0 3) 3 4) 7 1)
              NOP_OP 16 16) 16 16) 0 3) =
      if Int.lt (int_of_breg dst) (Int.repr 8)
        then int_of_breg dst
        else Int.sub (int_of_breg dst) (Int.repr 8).
Proof.
  intros.
  unfold MOV_R_OP, NOP_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + apply size_bitfield_insert; try lia.
        * prove_int.
        * unfold int_of_breg; destruct dst; prove_int.
      + unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 7%Z) (width0 := 1%Z) (pos1 := 0%Z) (width1 := 3%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 3%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 3%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite bitfield_insert_unsigned_bitfield_extract_same with
    (pos := 0%Z) (width := 3%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  instantiate (1 := Int.bitfield_insert 0 3 Int.zero
    (if Int.lt (int_of_breg dst) (Int.repr 8) then int_of_breg dst else Int.sub (int_of_breg dst) (Int.repr 8))).
  destruct dst; repeat int_true_false.
Qed.

Lemma decode_arm32_MOV_R_OP_dst:
  forall dst src,
int2ireg
    (encode_arm32
       (decode_arm32
          (decode_arm32
             (encode_arm32
                (encode_arm32
                   (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
                   (encode_arm32 (int_of_ireg src)
                      (encode_arm32
                         (if Int.lt (int_of_breg dst) (Int.repr 8)
                          then int_of_breg dst
                          else Int.sub (int_of_breg dst) (Int.repr 8)) MOV_R_OP 0 3) 3 4) 7 1)
                NOP_OP 16 16) 16 16) 7 1)
       (decode_arm32
          (decode_arm32
             (encode_arm32
                (encode_arm32
                   (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
                   (encode_arm32 (int_of_ireg src)
                      (encode_arm32
                         (if Int.lt (int_of_breg dst) (Int.repr 8)
                          then int_of_breg dst
                          else Int.sub (int_of_breg dst) (Int.repr 8)) MOV_R_OP 0 3) 3 4) 7 1)
                NOP_OP 16 16) 16 16) 0 3) 3 1)  = Some (ireg_of_breg dst).
Proof.
  intros.
  rewrite decode_arm32_MOV_R_OP_dst_4.
  rewrite decode_arm32_MOV_R_OP_dst_0_3.
  unfold encode_arm32.

  destruct dst; unfold int_of_breg; simpl; prove_int_bit;
  unfold int2ireg; auto.
Qed.

Lemma decode_arm32_MOV_R_OP_src:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
                (encode_arm32 (int_of_ireg src)
                   (encode_arm32
                      (if Int.lt (int_of_breg dst) (Int.repr 8)
                       then int_of_breg dst
                       else Int.sub (int_of_breg dst) (Int.repr 8)) MOV_R_OP 0 3) 3 4) 7 1)
             NOP_OP 16 16) 16 16) 3 4) = Some src.
Proof.
  intros.
  unfold MOV_R_OP, NOP_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + apply size_bitfield_insert; try lia.
        * prove_int.
        * unfold int_of_breg; destruct dst; prove_int.
      + unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 7%Z) (width0 := 1%Z) (pos1 := 3%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  simpl.
  erewrite bitfield_insert_unsigned_bitfield_extract_same with
    (pos := 3%Z) (width := 4%Z) (p := Int.bitfield_insert 3 4 Int.zero (int_of_ireg src))
    (i := (Int.bitfield_insert 0 3 (Int.repr 17920)
           (if Int.lt (int_of_breg dst) (Int.repr 8)
            then int_of_breg dst
            else Int.sub (int_of_breg dst) (Int.repr 8))));
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  - destruct src; repeat int_true_false.
  - assert (Heq: (Int.unsigned_bitfield_extract 3 4 (Int.bitfield_insert 3 4 Int.zero
      (int_of_ireg src))) = (int_of_ireg src)).
    + erewrite bitfield_insert_unsigned_bitfield_extract_same with
      (pos := 3%Z) (width := 4%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.

      instantiate (1 := Int.bitfield_insert 3 4 Int.zero
        (int_of_ireg src)).
      destruct src; repeat int_true_false.
    + rewrite Heq.
      f_equal.
Qed.

Lemma decode_arm32_MOV_R_OP_dst_8_2:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
                (encode_arm32 (int_of_ireg src)
                   (encode_arm32
                      (if Int.lt (int_of_breg dst) (Int.repr 8)
                       then int_of_breg dst
                       else Int.sub (int_of_breg dst) (Int.repr 8)) MOV_R_OP 0 3) 3 4) 7 1)
             NOP_OP 16 16) 16 16) 8 2) = Int.repr 2.
Proof.
  intros.
  unfold MOV_R_OP, NOP_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + apply size_bitfield_insert; try lia.
        * prove_int.
        * unfold int_of_breg; destruct dst; prove_int.
      + unfold int_of_ireg, ireg_of_breg; destruct src; prove_int.
    - unfold int_of_breg; destruct dst; prove_int.
  }

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 7%Z) (width0 := 1%Z) (pos1 := 8%Z) (width1 := 2%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 3%Z) (width0 := 4%Z) (pos1 := 8%Z) (width1 := 2%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 0%Z) (width0 := 3%Z) (pos1 := 8%Z) (width1 := 2%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].

  auto.
Qed.

Lemma decode_mov_r:
  forall dst src,
    decode_thumb
      (encode_arm32
         (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
            (encode_arm32 (int_of_ireg src)
               (encode_arm32
                  (if Int.lt (int_of_breg dst) (Int.repr 8)
                   then int_of_breg dst
                   else Int.sub (int_of_breg dst) (Int.repr 8)) MOV_R_OP 0 3) 3 4) 7 1) NOP_OP 16
         16) = Some (Pmov (ireg_of_breg dst) (SOreg src)).
Proof.
  intros.
  unfold decode_thumb.
  rewrite decode_arm32_MOV_R_OP_11_5.
  rewrite Int.eq_true.
  rewrite decode_arm32_MOV_R_OP_NOP_OP.
  rewrite Int.eq_true.
  unfold decode_thumb1.
  rewrite decode_arm32_MOV_R_OP_10_6.
  rewrite Int.eq_true.

  rewrite decode_arm32_MOV_R_OP_dst.
  rewrite decode_arm32_MOV_R_OP_src.
  rewrite decode_arm32_MOV_R_OP_dst_8_2.
  replace (Int.eq (Int.repr 2) Int.zero) with false by reflexivity.
  replace (Int.eq (Int.repr 2) Int.one) with false by reflexivity.
  rewrite Int.eq_true.
  f_equal.
Qed.


Lemma decode_arm32_DIV_R_OP_HI_11_5:
  forall dst src,
  (decode_arm32
       (encode_arm32 (encode_arm32 (int_of_ireg src) (encode_arm32 (int_of_breg dst) UDIV_HI_OP 8 4) 0 4)
          (encode_arm32 (int_of_breg dst) UDIV_LO_OP 0 4) 16 16) 11 5) = Int.repr 31.
Proof.
  intros.
  unfold UDIV_LO_OP, decode_arm32, encode_arm32.
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

Lemma decode_arm32_DIV_R_OP_LO_11_5:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_ireg src) (encode_arm32 (int_of_breg dst) UDIV_HI_OP 8 4) 0 4)
             (encode_arm32 (int_of_breg dst) UDIV_LO_OP 0 4) 16 16) 0 16) 11 5) =
    (Int.repr 31).
Proof.
  intros.
  unfold decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; auto.
Qed.

Lemma decode_arm32_DIV_R_OP_9_2:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_ireg src) (encode_arm32 (int_of_breg dst) UDIV_HI_OP 8 4) 0 4)
             (encode_arm32 (int_of_breg dst) UDIV_LO_OP 0 4) 16 16) 0 16) 9 2) = Int.one.
Proof.
  intros.
  unfold UDIV_LO_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; auto.
Qed.

Lemma decode_arm32_DIV_R_OP_dst:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_ireg src) (encode_arm32 (int_of_breg dst) UDIV_HI_OP 8 4) 0 4)
             (encode_arm32 (int_of_breg dst) UDIV_LO_OP 0 4) 16 16) 0 16) 0 4) = Some (ireg_of_breg dst).
Proof.
  intros.
  unfold UDIV_LO_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite unsigned_bitfield_extract_low_same with (width := 16%Z);
    [ | replace Int.zwordsize with 32%Z by reflexivity; lia | ].

  - erewrite unsigned_bitfield_extract_bitfield_insert_same;
      replace Int.zwordsize with 32%Z by reflexivity; try lia.
    + apply int2ireg_int_of_breg_same.
    + destruct dst; prove_int.

  - destruct dst; prove_int.
Qed.

Lemma decode_arm32_DIV_R_OP_src:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_ireg src) (encode_arm32 (int_of_breg dst) UDIV_HI_OP 8 4) 0 4)
             (encode_arm32 (int_of_breg dst) UDIV_LO_OP 0 4) 16 16) 16 16) 0 4) = Some src.
Proof.
  intros.
  unfold UDIV_HI_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - destruct dst; prove_int.
    - destruct src; prove_int.
  }
  erewrite unsigned_bitfield_extract_bitfield_insert_same;
      replace Int.zwordsize with 32%Z by reflexivity; try lia.
    + apply int2ireg_int_of_ireg_same.
    + destruct src; prove_int.
Qed.

Lemma decode_arm32_DIV_R_OP_dst2:
  forall dst src,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_ireg src) (encode_arm32 (int_of_breg dst) UDIV_HI_OP 8 4) 0 4)
             (encode_arm32 (int_of_breg dst) UDIV_LO_OP 0 4) 16 16) 16 16) 8 4) = Some (ireg_of_breg dst).
Proof.
  intros.
  unfold UDIV_HI_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct dst; prove_int.
    - unfold int_of_breg; destruct src; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 8%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 8%Z) (width := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{ unfold int_of_breg; destruct dst; prove_int. }

  apply int2ireg_int_of_breg_same.
Qed.

Lemma decode_arm32_DIV_R_OP_12_4:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_ireg src) (encode_arm32 (int_of_breg dst) UDIV_HI_OP 8 4) 0 4)
             (encode_arm32 (int_of_breg dst) UDIV_LO_OP 0 4) 16 16) 16 16) 12 4) = (Int.repr 15).
Proof.
  intros.
  unfold UDIV_HI_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct dst; prove_int.
    - unfold int_of_breg; destruct src; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 12%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 12%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  auto.
Qed.

Lemma decode_arm32_DIV_R_OP_4_4:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_ireg src) (encode_arm32 (int_of_breg dst) UDIV_HI_OP 8 4) 0 4)
             (encode_arm32 (int_of_breg dst) UDIV_LO_OP 0 4) 16 16) 16 16) 4 4) = Int.repr 15.
Proof.
  intros.
  unfold UDIV_HI_OP, decode_arm32, encode_arm32.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - unfold int_of_ireg, ireg_of_breg; destruct dst; prove_int.
    - unfold int_of_breg; destruct src; prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 4%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 4%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  auto.
Qed.

Lemma decode_arm32_DIV_R_OP_4_1:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_ireg src) (encode_arm32 (int_of_breg dst) UDIV_HI_OP 8 4) 0 4)
             (encode_arm32 (int_of_breg dst) UDIV_LO_OP 0 4) 16 16) 0 16) 4 1) = Int.one.
Proof.
  intros.
  unfold UDIV_LO_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; auto.
Qed.

Lemma decode_arm32_DIV_R_OP_5_4:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (int_of_ireg src) (encode_arm32 (int_of_breg dst) UDIV_HI_OP 8 4) 0 4)
             (encode_arm32 (int_of_breg dst) UDIV_LO_OP 0 4) 16 16) 0 16) 5 4) =
       Int.repr 13.
Proof.
  intros.
  unfold UDIV_LO_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; repeat int_true_false; f_equal.
Qed.

Lemma decode_div_r:
  forall dst src,
    decode_thumb
      (encode_arm32 (encode_arm32 (int_of_ireg src) (encode_arm32 (int_of_breg dst) UDIV_HI_OP 8 4) 0 4)
         (encode_arm32 (int_of_breg dst) UDIV_LO_OP 0 4) 16 16) =
    Some (Pudiv (ireg_of_breg dst) (ireg_of_breg dst) src).
Proof.
  intros.
  unfold decode_thumb.
  rewrite decode_arm32_DIV_R_OP_HI_11_5.
  replace (Int.eq (Int.repr 31) (Int.repr 23)) with false by reflexivity; simpl.
  unfold decode_thumb2.
  rewrite decode_arm32_DIV_R_OP_LO_11_5.
  replace (Int.eq (Int.repr 31) (Int.repr 29)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 30)) with false by reflexivity; simpl.
  rewrite Int.eq_true.

  rewrite decode_arm32_DIV_R_OP_9_2.
  replace (Int.eq Int.one Int.zero) with false by reflexivity; simpl.
  rewrite Int.eq_true.
  rewrite decode_arm32_DIV_R_OP_dst.
  rewrite decode_arm32_DIV_R_OP_src.
  rewrite decode_arm32_DIV_R_OP_dst2.
  rewrite decode_arm32_DIV_R_OP_12_4.
  rewrite Int.eq_true.
  rewrite decode_arm32_DIV_R_OP_4_4.
  replace (Int.eq (Int.repr 15) Int.zero) with false by reflexivity; simpl.
  rewrite Int.eq_true.
  rewrite decode_arm32_DIV_R_OP_5_4.
  rewrite decode_arm32_DIV_R_OP_4_1.
  rewrite Int.eq_true.
  rewrite Int.eq_true.
  rewrite Bool.andb_true_l.
  f_equal.
Qed.


Lemma decode_arm32_LSL_R_OP_HI_11_5:
  forall dst src op,
    op = LSL_R_OP \/ op = LSR_R_OP \/ op = ASR_R_OP ->
  (decode_arm32
       (encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12 4)
          (encode_arm32 (int_of_breg dst) op 0 4) 16 16) 11 5) = Int.repr 31.
Proof.
  unfold LSL_R_OP, LSR_R_OP, ASR_R_OP, decode_arm32, encode_arm32.
  intros.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 0%Z) (width0 := 4%Z) (pos1 := 11%Z) (width1 := 5%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct H as [H | H]; [| destruct H as [H | H]]; subst op; auto.
Qed.

Lemma decode_arm32_LSL_R_OP_LO_11_5:
  forall dst src op,
    op = LSL_R_OP \/ op = LSR_R_OP \/ op = ASR_R_OP ->
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12 4)
             (encode_arm32 (int_of_breg dst) op 0 4) 16 16) 0 16) 11 5) =
    (Int.repr 31).
Proof.
  unfold LSL_R_OP, LSR_R_OP, ASR_R_OP, decode_arm32, encode_arm32.
  intros.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct H as [H | H]; [| destruct H as [H | H]]; subst op; destruct dst; auto.
Qed.

Lemma decode_arm32_LSL_R_OP_9_2:
  forall dst src op,
    op = LSL_R_OP \/ op = LSR_R_OP \/ op = ASR_R_OP ->
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12 4)
             (encode_arm32 (int_of_breg dst) op 0 4) 16 16) 0 16) 9 2) = Int.one.
Proof.
  unfold LSL_R_OP, LSR_R_OP, ASR_R_OP, decode_arm32, encode_arm32.
  intros.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct H as [H | H]; [| destruct H as [H | H]]; subst op; destruct dst; auto.
Qed.

Lemma decode_arm32_LSL_R_OP_dst:
  forall dst src op,
    op = LSL_R_OP \/ op = LSR_R_OP \/ op = ASR_R_OP ->
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12 4)
             (encode_arm32 (int_of_breg dst) op 0 4) 16 16) 0 16) 0 4) = Some (ireg_of_breg dst).
Proof.
  unfold LSL_R_OP, LSR_R_OP, ASR_R_OP, decode_arm32, encode_arm32.
  intros.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite unsigned_bitfield_extract_low_same with (width := 16%Z);
    [ | replace Int.zwordsize with 32%Z by reflexivity; lia | ].

  - erewrite unsigned_bitfield_extract_bitfield_insert_same;
      replace Int.zwordsize with 32%Z by reflexivity; try lia.
    + apply int2ireg_int_of_breg_same.
    + destruct dst; prove_int.

  - destruct H as [H | H]; [| destruct H as [H | H]]; subst op; destruct dst; prove_int.
Qed.

Lemma decode_arm32_LSL_R_OP_src:
  forall dst src op,
    op = LSL_R_OP \/ op = LSR_R_OP \/ op = ASR_R_OP ->
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12 4)
             (encode_arm32 (int_of_breg dst) op 0 4) 16 16) 16 16) 0 4) = Some src.
Proof.
  unfold LSL_R_OP, LSR_R_OP, ASR_R_OP, decode_arm32, encode_arm32.
  intros.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + destruct src; prove_int.
      + destruct dst; prove_int.
    - prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 12%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 0%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct H as [H | H]; [| destruct H as [H | H]]; subst op; destruct src; auto.
Qed.

Lemma decode_arm32_LSL_R_OP_dst2:
  forall dst src op,
    int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12 4)
             (encode_arm32 (int_of_breg dst) op 0 4) 16 16) 16 16) 8 4) = Some (ireg_of_breg dst).
Proof.
  unfold decode_arm32, encode_arm32.
  intros.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + destruct src; prove_int.
      + destruct dst; prove_int.
    - prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 12%Z) (width0 := 4%Z) (pos1 := 8%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 8%Z) (width := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{ unfold int_of_breg; destruct dst; prove_int. }

  apply int2ireg_int_of_breg_same.
Qed.

Lemma decode_arm32_LSL_R_OP_12_4:
  forall dst src op,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12 4)
             (encode_arm32 (int_of_breg dst) op 0 4) 16 16) 16 16) 12 4) = (Int.repr 15).
Proof.
  unfold decode_arm32, encode_arm32.
  intros.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + destruct src; prove_int.
      + destruct dst; prove_int.
    - prove_int.
  }

  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 12%Z) (width := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  prove_int.
Qed.

Lemma decode_arm32_LSL_R_OP_4_4:
  forall dst src op,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12 4)
             (encode_arm32 (int_of_breg dst) op 0 4) 16 16) 16 16) 4 4) = Int.zero.
Proof.
  unfold decode_arm32, encode_arm32.
  intros.
  erewrite unsigned_bitfield_extract_bitfield_insert_same with
    (pos := 16%Z) (width := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
  2:{
    apply size_bitfield_insert; try lia.
    - apply size_bitfield_insert; try lia.
      + destruct src; prove_int.
      + destruct dst; prove_int.
    - prove_int.
  }
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 12%Z) (width0 := 4%Z) (pos1 := 4%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 8%Z) (width0 := 4%Z) (pos1 := 4%Z) (width1 := 4%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct src; auto.
Qed.

Lemma decode_arm32_LSL_R_OP_4_1:
  forall dst src op,
    op = LSL_R_OP \/ op = LSR_R_OP \/ op = ASR_R_OP ->
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12 4)
             (encode_arm32 (int_of_breg dst) op 0 4) 16 16) 0 16) 4 1) = Int.zero.
Proof.
  unfold LSL_R_OP, LSR_R_OP, ASR_R_OP, decode_arm32, encode_arm32.
  intros.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct H as [H | H]; [| destruct H as [H | H]]; subst op; destruct dst; auto.
Qed.

Lemma decode_arm32_LSL_R_OP_5_4:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12 4)
             (encode_arm32 (int_of_breg dst) LSL_R_OP 0 4) 16 16) 0 16) 5 4) = Int.zero.
Proof.
  intros.
  unfold LSL_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; repeat int_true_false; f_equal.
Qed.

Lemma decode_arm32_LSR_R_OP_5_4:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12 4)
             (encode_arm32 (int_of_breg dst) LSR_R_OP 0 4) 16 16) 0 16) 5 4) = Int.one.
Proof.
  intros.
  unfold LSR_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; repeat int_true_false; f_equal.
Qed.

Lemma decode_arm32_ASR_R_OP_5_4:
  forall dst src,
    (decode_arm32
       (decode_arm32
          (encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12 4)
             (encode_arm32 (int_of_breg dst) ASR_R_OP 0 4) 16 16) 0 16) 5 4) = Int.repr 2.
Proof.
  intros.
  unfold ASR_R_OP, decode_arm32, encode_arm32.
  erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
    (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
    replace Int.zwordsize with 32%Z by reflexivity; try lia;
      [| reflexivity | reflexivity ].
  destruct dst; simpl; repeat int_true_false; f_equal.
Qed.

Lemma decode_lsl_r:
  forall dst src,
    decode_thumb
      (encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12 4)
         (encode_arm32 (int_of_breg dst) LSL_R_OP 0 4) 16 16) = Some (Plsl (ireg_of_breg dst) (ireg_of_breg dst) src).
Proof.
  intros.
  unfold decode_thumb.
  rewrite decode_arm32_LSL_R_OP_HI_11_5; [| auto].
  replace (Int.eq (Int.repr 31) (Int.repr 23)) with false by reflexivity; simpl.
  unfold decode_thumb2.
  rewrite decode_arm32_LSL_R_OP_LO_11_5; [| auto].
  replace (Int.eq (Int.repr 31) (Int.repr 29)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 30)) with false by reflexivity; simpl.
  rewrite Int.eq_true.

  rewrite decode_arm32_LSL_R_OP_9_2; [| auto].
  replace (Int.eq Int.one Int.zero) with false by reflexivity; simpl.
  rewrite Int.eq_true.
  rewrite decode_arm32_LSL_R_OP_dst; [| auto].
  rewrite decode_arm32_LSL_R_OP_src; [| auto].
  rewrite decode_arm32_LSL_R_OP_dst2.
  rewrite decode_arm32_LSL_R_OP_12_4.
  rewrite Int.eq_true.
  rewrite decode_arm32_LSL_R_OP_4_4.
  rewrite Int.eq_true.
  rewrite decode_arm32_LSL_R_OP_4_1; [| auto].
  rewrite Int.eq_true.
  rewrite decode_arm32_LSL_R_OP_5_4.
  rewrite Int.eq_true.
  f_equal.
Qed.

Lemma decode_lsr_r:
  forall dst src,
    decode_thumb
      (encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12 4)
         (encode_arm32 (int_of_breg dst) LSR_R_OP 0 4) 16 16) = Some (Plsr (ireg_of_breg dst) (ireg_of_breg dst) src).
Proof.
  intros.
  unfold decode_thumb.
  rewrite decode_arm32_LSL_R_OP_HI_11_5; [| auto].
  replace (Int.eq (Int.repr 31) (Int.repr 23)) with false by reflexivity; simpl.
  unfold decode_thumb2.
  rewrite decode_arm32_LSL_R_OP_LO_11_5; [| auto].
  replace (Int.eq (Int.repr 31) (Int.repr 29)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 30)) with false by reflexivity; simpl.
  rewrite Int.eq_true.

  rewrite decode_arm32_LSL_R_OP_9_2; [| auto].
  replace (Int.eq Int.one Int.zero) with false by reflexivity; simpl.
  rewrite Int.eq_true.
  rewrite decode_arm32_LSL_R_OP_dst; [| auto].
  rewrite decode_arm32_LSL_R_OP_src; [| auto].
  rewrite decode_arm32_LSL_R_OP_dst2.
  rewrite decode_arm32_LSL_R_OP_12_4.
  rewrite Int.eq_true.
  rewrite decode_arm32_LSL_R_OP_4_4.
  rewrite Int.eq_true.
  rewrite decode_arm32_LSL_R_OP_4_1; [| auto].
  rewrite Int.eq_true.
  rewrite decode_arm32_LSR_R_OP_5_4.
  replace (Int.eq Int.one Int.zero) with false by reflexivity; simpl.
  rewrite Int.eq_true.
  f_equal.
Qed.

Lemma decode_asr_r:
  forall dst src,
    decode_thumb
      (encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4) 12 4)
         (encode_arm32 (int_of_breg dst) ASR_R_OP 0 4) 16 16) = Some (Pasr (ireg_of_breg dst) (ireg_of_breg dst) src).
Proof.
  intros.
  unfold decode_thumb.
  rewrite decode_arm32_LSL_R_OP_HI_11_5; [| auto].
  replace (Int.eq (Int.repr 31) (Int.repr 23)) with false by reflexivity; simpl.
  unfold decode_thumb2.
  rewrite decode_arm32_LSL_R_OP_LO_11_5; [| auto].
  replace (Int.eq (Int.repr 31) (Int.repr 29)) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 31) (Int.repr 30)) with false by reflexivity; simpl.
  rewrite Int.eq_true.

  rewrite decode_arm32_LSL_R_OP_9_2; [| auto].
  replace (Int.eq Int.one Int.zero) with false by reflexivity; simpl.
  rewrite Int.eq_true.
  rewrite decode_arm32_LSL_R_OP_dst; [| auto].
  rewrite decode_arm32_LSL_R_OP_src; [| auto].
  rewrite decode_arm32_LSL_R_OP_dst2.
  rewrite decode_arm32_LSL_R_OP_12_4.
  rewrite Int.eq_true.
  rewrite decode_arm32_LSL_R_OP_4_4.
  rewrite Int.eq_true.
  rewrite decode_arm32_LSL_R_OP_4_1; [| auto].
  rewrite Int.eq_true.
  rewrite decode_arm32_ASR_R_OP_5_4.
  replace (Int.eq (Int.repr 2) Int.zero) with false by reflexivity; simpl.
  replace (Int.eq (Int.repr 2) Int.one) with false by reflexivity; simpl.
  rewrite Int.eq_true.
  f_equal.
Qed.

Lemma decode_mov_12_1:
  decode_thumb
    (encode_arm32
       (encode_arm32 Int.one
          (encode_arm32 Int.one (encode_arm32 (Int.repr 4) MOV_R_OP 0 3) 3 4) 7 1) NOP_OP 16 16) =
    Some (Pmov IR12 (SOreg IR1)).
Proof.
  unfold decode_thumb.
  rewrite decode_arm32_MOV_R_OP_11_5.
  rewrite Int.eq_true.
  rewrite decode_arm32_MOV_R_OP_NOP_OP.
  rewrite Int.eq_true.
  unfold decode_thumb1.

  assert (Heq: (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 Int.one
                (encode_arm32 Int.one (encode_arm32 (Int.repr 4) MOV_R_OP 0 3) 3 4) 7 1) NOP_OP
             16 16) 16 16) 10 6) = Int.repr 17). {
    unfold MOV_R_OP, decode_arm32, encode_arm32.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
    unfold Int.one; prove_int.
  }
  rewrite Heq; clear Heq.
  rewrite Int.eq_true.

  assert (Heq: (decode_arm32
          (decode_arm32
             (encode_arm32
                (encode_arm32 Int.one
                   (encode_arm32 Int.one (encode_arm32 (Int.repr 4) MOV_R_OP 0 3) 3 4) 7 1)
                NOP_OP 16 16) 16 16) 7 1) = Int.one). {
    unfold MOV_R_OP, NOP_OP, decode_arm32, encode_arm32.
    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
    unfold Int.one; prove_int.
  }
  rewrite Heq; clear Heq.

  assert (Heq: (decode_arm32
          (decode_arm32
             (encode_arm32
                (encode_arm32 Int.one
                   (encode_arm32 Int.one (encode_arm32 (Int.repr 4) MOV_R_OP 0 3) 3 4) 7 1)
                NOP_OP 16 16) 16 16) 0 3) = Int.repr 4). {
    unfold MOV_R_OP, NOP_OP, decode_arm32, encode_arm32.
    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
    unfold Int.one; prove_int.
  }
  rewrite Heq; clear Heq.
  assert (Heq: (encode_arm32 Int.one (Int.repr 4) 3 1) = Int.repr 12). {
    unfold encode_arm32, Int.one.
    auto.
  }
  rewrite Heq; clear Heq.

  assert (Heq: int2ireg (Int.repr 12) = Some IR12). {
    unfold int2ireg.
    simpl; auto.
  }
  rewrite Heq; clear Heq.
  assert (Heq: int2ireg
    (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 Int.one
                (encode_arm32 Int.one (encode_arm32 (Int.repr 4) MOV_R_OP 0 3) 3 4) 7 1) NOP_OP
             16 16) 16 16) 3 4) = Some IR1). {
    unfold MOV_R_OP, NOP_OP, decode_arm32, encode_arm32, Int.one.
    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
    prove_int.
  }
  rewrite Heq; clear Heq.

  assert (Heq: (decode_arm32
       (decode_arm32
          (encode_arm32
             (encode_arm32 Int.one
                (encode_arm32 Int.one (encode_arm32 (Int.repr 4) MOV_R_OP 0 3) 3 4) 7 1) NOP_OP
             16 16) 16 16) 8 2) = Int.repr 2). {
    unfold MOV_R_OP, NOP_OP, decode_arm32, encode_arm32, Int.one.
    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
    prove_int.
  }
  rewrite Heq; clear Heq.
  replace (Int.eq (Int.repr 2) Int.zero) with false by reflexivity.
  replace (Int.eq (Int.repr 2) Int.one) with false by reflexivity.
  rewrite Int.eq_true.
  f_equal.
Qed.

Lemma decode_bx:
  decode_thumb (encode_arm32 (encode_arm32 (int_of_ireg IR14) BX_OP 3 4) NOP_OP 16 16) =
  Some (Pbreg IR14).
Proof.
  unfold decode_thumb.
  assert (Heq: (decode_arm32 (encode_arm32 (encode_arm32 (int_of_ireg IR14) BX_OP 3 4) NOP_OP 16 16) 11 5) = (Int.repr 23)). {
    unfold decode_arm32, encode_arm32, NOP_OP.
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 11%Z) (width1 := 5%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    auto.
  }
  rewrite Heq; clear Heq.
  rewrite Int.eq_true.
  assert (Heq: (decode_arm32 (encode_arm32 (encode_arm32 (int_of_ireg IR14) BX_OP 3 4) NOP_OP 16 16) 0 16) = NOP_OP). {
    unfold decode_arm32, encode_arm32, NOP_OP.
    erewrite bitfield_insert_unsigned_bitfield_extract_same_outside with
      (pos0 := 16%Z) (width0 := 16%Z) (pos1 := 0%Z) (width1 := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia;
        [| reflexivity | reflexivity ].
    auto.
  }
  rewrite Heq; clear Heq.

  rewrite Int.eq_true.
  unfold decode_thumb1.
  assert (Heq: (decode_arm32
       (decode_arm32 (encode_arm32 (encode_arm32 (int_of_ireg IR14) BX_OP 3 4) NOP_OP 16 16) 16
          16) 10 6) = (Int.repr 17)). {
    unfold decode_arm32, encode_arm32, NOP_OP.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
    prove_int.
  }
  rewrite Heq; clear Heq.

  rewrite Int.eq_true.
  assert (Heq: (decode_arm32
          (decode_arm32 (encode_arm32 (encode_arm32 (int_of_ireg IR14) BX_OP 3 4) NOP_OP 16 16)
             16 16) 7 1) = Int.zero). {
    unfold decode_arm32, encode_arm32, NOP_OP.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
    prove_int.
  }
  rewrite Heq; clear Heq.

  assert (Heq: (decode_arm32
          (decode_arm32 (encode_arm32 (encode_arm32 (int_of_ireg IR14) BX_OP 3 4) NOP_OP 16 16)
             16 16) 0 3) = Int.repr 0). {
    unfold decode_arm32, encode_arm32, NOP_OP, BX_OP.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
    prove_int.
  }
  rewrite Heq; clear Heq.

  assert (Heq: int2ireg (encode_arm32 Int.zero (Int.repr 0) 3 1) = Some IR0). {
    unfold encode_arm32, Int.zero.
    auto.
  }
  rewrite Heq; clear Heq.

  assert (Heq: int2ireg
    (decode_arm32
       (decode_arm32 (encode_arm32 (encode_arm32 (int_of_ireg IR14) BX_OP 3 4) NOP_OP 16 16) 16
          16) 3 4) = Some IR14). {
    unfold decode_arm32, encode_arm32, NOP_OP, BX_OP.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
    prove_int.
  }
  rewrite Heq; clear Heq.

  assert (Heq: (decode_arm32
       (decode_arm32 (encode_arm32 (encode_arm32 (int_of_ireg IR14) BX_OP 3 4) NOP_OP 16 16) 16
          16) 8 2) = Int.repr 3). {
    unfold decode_arm32, encode_arm32, NOP_OP, BX_OP.

    erewrite unsigned_bitfield_extract_bitfield_insert_same with
      (pos := 16%Z) (width := 16%Z);
      replace Int.zwordsize with 32%Z by reflexivity; try lia; eauto.
    prove_int.
  }
  rewrite Heq; clear Heq.

  repeat int_true_false.
  reflexivity.
Qed.