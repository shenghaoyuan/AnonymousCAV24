From compcert.lib Require Import Integers Coqlib Maps.
From compcert.common Require Import AST Values Memory.
From compcert.arm Require Import AsmSyntax ABinSem BinDecode BinSyntax Conventions1 Machregs.

From bpf.comm Require Import rBPFMemType JITCall.
From bpf.rbpf32 Require Import TSSyntax JITConfig.
From bpf.jit Require Import Arm32Reg ThumbInsOp ThumbJIT WholeCompiler.
From bpf.jit Require Import ThumbJITLtac ABMemory TSSemanticsB ThumbJITProofLemma0 TSSemanticsBproofdef.
From bpf.jit Require Import ThumbDecodeEncodeALU ThumbDecodeEncodeALU0 ThumbDecodeEncodeMEM TSSemanticsBproof6.
From Coq Require Import ZArith Lia List ListSet.

Open Scope nat_scope.
Open Scope asm.
Import ListNotations.

Lemma exec_alu32_add_r:
  forall (rs0 rs1: regset) (dst src: breg) i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.add (rs0 dst) (rs0 src) = Vint i)
    (Hsave : jit_call_save_reg dst src ld_set st_set = (l2, ld_set2, st_set2))
    (Hl1 : l2 ++
      [encode_arm32
         (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
            (encode_arm32 (int_of_ireg (ireg_of_breg src))
               (encode_arm32
                  (if Int.lt (int_of_breg dst) (Int.repr 8)
                   then int_of_breg dst
                   else Int.sub (int_of_breg dst) (Int.repr 8)) ADD_R_OP 0 3) 3 4) 7 1) NOP_OP 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof0.v *)
Admitted.

Lemma exec_alu32_sub_r:
  forall (rs0 rs1: regset) (dst src: breg) i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.sub (rs0 dst) (rs0 src) = Vint i)
    (Hsave : jit_call_save_reg dst src ld_set st_set = (l2, ld_set2, st_set2))
    (Hl1 : l2 ++
      [encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg (ireg_of_breg src)) 8 4)
         (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof1.v *)
Admitted.

Lemma exec_alu32_mul:
  forall (rs0 rs1: regset) (dst src: breg) i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.mul (rs0 dst) (rs0 src) = Vint i)
    (Hsave : jit_call_save_reg dst src ld_set st_set = (l2, ld_set2, st_set2))
    (Hl1 : l2 ++
      [encode_arm32
         (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg (ireg_of_breg src)) 8 4) 12 4)
         (encode_arm32 (int_of_breg dst) MUL_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof2.v *)
Admitted.

Lemma exec_alu32_orr_r:
  forall (rs0 rs1: regset) (dst src: breg) i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.or (rs0 dst) (rs0 src) = Vint i)
    (Hsave : jit_call_save_reg dst src ld_set st_set = (l2, ld_set2, st_set2))
    (Hl1 : l2 ++
      [encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg (ireg_of_breg src)) 8 4)
         (encode_arm32 (int_of_breg dst) ORR_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof3.v *)
Admitted.

Lemma exec_alu32_and_r:
  forall (rs0 rs1: regset) (dst src: breg) i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.and (rs0 dst) (rs0 src) = Vint i)
    (Hsave : jit_call_save_reg dst src ld_set st_set = (l2, ld_set2, st_set2))
    (Hl1 : l2 ++
      [encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg (ireg_of_breg src)) 8 4)
         (encode_arm32 (int_of_breg dst) AND_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof4.v *)
Admitted.

Lemma exec_alu32_xor_r:
  forall (rs0 rs1: regset) (dst src: breg) i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.xor (rs0 dst) (rs0 src) = Vint i)
    (Hsave : jit_call_save_reg dst src ld_set st_set = (l2, ld_set2, st_set2))
    (Hl1 : l2 ++
      [encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg (ireg_of_breg src)) 8 4)
         (encode_arm32 (int_of_breg dst) EOR_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof5.v *)
Admitted.

Lemma exec_alu32_mov_r:
  forall (rs0 rs1: regset) (dst src: breg) i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : rs0 src = Vint i)
    (Hsave : jit_call_save_reg dst src ld_set st_set = (l2, ld_set2, st_set2))
    (HREG_NEQ : dst <> src)
    (Hl1 : l2 ++
      [encode_arm32
         (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
            (encode_arm32 (int_of_ireg (ireg_of_breg src))
               (encode_arm32
                  (if Int.lt (int_of_breg dst) (Int.repr 8)
                   then int_of_breg dst
                   else Int.sub (int_of_breg dst) (Int.repr 8)) MOV_R_OP 0 3) 3 4) 7 1) NOP_OP 16
         16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof7.v *)
Admitted.

Lemma exec_alu32_add_i_0:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.add (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true)
    (Hl1 : l2 ++
      [encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4)
         (encode_arm32 (int_of_breg dst) ADD_I_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof8.v *)
Admitted.

Lemma exec_alu32_add_r1:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.add (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = false)
    (Hhi_0 : Int.eq (decode_arm32 si 0 16) si = true)
    (Hl1 : l2 ++
      [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      encode_arm32
        (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
           (encode_arm32 (int_of_ireg IR11)
              (encode_arm32
                 (if Int.lt (int_of_breg dst) (Int.repr 8)
                  then int_of_breg dst
                  else Int.sub (int_of_breg dst) (Int.repr 8)) ADD_R_OP 0 3) 3 4) 7 1) NOP_OP 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof8.v *)
Admitted.

Lemma exec_alu32_add_r2:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.add (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = false)
    (Hl1 : l2 ++
      [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      mov_int_to_movwt (decode_arm32 si 16 16) IR11 MOVT_OP;
      encode_arm32
        (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
           (encode_arm32 (int_of_ireg IR11)
              (encode_arm32
                 (if Int.lt (int_of_breg dst) (Int.repr 8)
                  then int_of_breg dst
                  else Int.sub (int_of_breg dst) (Int.repr 8)) ADD_R_OP 0 3) 3 4) 7 1) NOP_OP 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof8.v *)
Admitted.

Lemma exec_alu32_sub_i_0:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.sub (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true)
    (Hl1 : l2 ++
      [encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) SUB_I_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof9.v *)
Admitted.

Lemma exec_alu32_sub_r1:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.sub (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = false)
    (Hhi_0 : Int.eq (decode_arm32 si 0 16) si = true)
    (Hl1 : l2 ++
      [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4)
        (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof9.v *)
Admitted.

Lemma exec_alu32_sub_r2:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.sub (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = false)
    (Hl1 : l2 ++
      [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      mov_int_to_movwt (decode_arm32 si 16 16) IR11 MOVT_OP;
      encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4)
        (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof9.v *)
Admitted.

Lemma exec_alu32_mul_r1:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.mul (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hhi_0 : Int.eq (decode_arm32 si 0 16) si = true)
    (Hl1 : l2 ++
      [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4) 12 4)
        (encode_arm32 (int_of_breg dst) MUL_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof10.v *)
Admitted.

Lemma exec_alu32_mul_r2:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.mul (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hl1 : l2 ++
      [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      mov_int_to_movwt (decode_arm32 si 16 16) IR11 MOVT_OP;
      encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4) 12 4)
        (encode_arm32 (int_of_breg dst) MUL_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof10.v *)
Admitted.

Lemma exec_alu32_div_r1:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.divu (rs0 dst) (Vint si) = Some (Vint i))
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hzero_0 : Int.eq si Int.zero = false)
    (Hhi_0 : Int.eq (decode_arm32 si 0 16) si = true)
    (Hl1 : l2 ++
      [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      encode_arm32 (encode_arm32 (int_of_ireg IR11) (encode_arm32 (int_of_breg dst) UDIV_HI_OP 8 4) 0 4)
        (encode_arm32 (int_of_breg dst) UDIV_LO_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof11.v *)
Admitted.

Lemma exec_alu32_div_r2:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.divu (rs0 dst) (Vint si) = Some (Vint i))
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hzero_0 : Int.eq si Int.zero = false)
    (Hhi_0 : Int.eq (decode_arm32 si 0 16) si = false)
    (Hl1 : l2 ++
      [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      mov_int_to_movwt (decode_arm32 si 16 16) IR11 MOVT_OP;
      encode_arm32 (encode_arm32 (int_of_ireg IR11) (encode_arm32 (int_of_breg dst) UDIV_HI_OP 8 4) 0 4)
        (encode_arm32 (int_of_breg dst) UDIV_LO_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof11.v *)
Admitted.

Lemma exec_alu32_orr_i_0:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.or (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true)
    (Hl1 : l2 ++
      [encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) ORR_I_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof12.v *)
Admitted.

Lemma exec_alu32_orr_r1:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.or (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = false)
    (Hhi_0 : Int.eq (decode_arm32 si 0 16) si = true)
    (Hl1 : l2 ++ [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4)
        (encode_arm32 (int_of_breg dst) ORR_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof12.v *)
Admitted.

Lemma exec_alu32_orr_r2:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.or (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = false)
    (Hl1 : l2 ++
      [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      mov_int_to_movwt (decode_arm32 si 16 16) IR11 MOVT_OP;
      encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4)
        (encode_arm32 (int_of_breg dst) ORR_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof12.v *)
Admitted.

Lemma exec_alu32_and_i_0:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.and (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true)
    (Hl1 : l2 ++
      [encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) AND_I_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof13.v *)
Admitted.

Lemma exec_alu32_and_r1:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.and (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = false)
    (Hhi_0 : Int.eq (decode_arm32 si 0 16) si = true)
    (Hl1 : l2 ++ [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4)
        (encode_arm32 (int_of_breg dst) AND_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof13.v *)
Admitted.

Lemma exec_alu32_and_r2:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.and (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = false)
    (Hl1 : l2 ++
      [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      mov_int_to_movwt (decode_arm32 si 16 16) IR11 MOVT_OP;
      encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4)
        (encode_arm32 (int_of_breg dst) AND_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof13.v *)
Admitted.

Lemma exec_alu32_lsl_r1:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.shl (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hlt_32 : Int.cmpu Cle Int.zero si && Int.cmpu Clt si (Int.repr 32) = true)
    (Hl1 : l2 ++
      [mov_int_to_movwt si IR11 MOVW_OP;
      encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4) 12 4)
        (encode_arm32 (int_of_breg dst) LSL_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof14.v *)
Admitted.

Lemma exec_alu32_lsr_r1:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.shru (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hlt_32 : Int.cmpu Cle Int.zero si && Int.cmpu Clt si (Int.repr 32) = true)
    (Hl1 : l2 ++
      [mov_int_to_movwt si IR11 MOVW_OP;
      encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4) 12 4)
        (encode_arm32 (int_of_breg dst) LSR_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof14.v *)
Admitted.

Lemma exec_alu32_asr_r1:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.shr (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hlt_32 : Int.cmpu Cle Int.zero si && Int.cmpu Clt si (Int.repr 32) = true)
    (Hl1 : l2 ++
      [mov_int_to_movwt si IR11 MOVW_OP;
      encode_arm32 (encode_arm32 (Int.repr 15) (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4) 12 4)
        (encode_arm32 (int_of_breg dst) ASR_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof14.v *)
Admitted.


Lemma exec_alu32_neg_r1:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.neg (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hhi_0 : Int.eq (decode_arm32 si 0 16) si = true)
    (Hl1 : l2 ++
      [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      encode_arm32 (encode_arm32 (int_of_breg dst) Int.zero 8 4) (encode_arm32 (int_of_ireg IR11) RSB_I_OP 0 4) 16
        16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof15.v *)
Admitted.

Lemma exec_alu32_neg_r2:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.neg (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hl1 : l2 ++
      [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      mov_int_to_movwt (decode_arm32 si 16 16) IR11 MOVT_OP;
      encode_arm32 (encode_arm32 (int_of_breg dst) Int.zero 8 4) (encode_arm32 (int_of_ireg IR11) RSB_I_OP 0 4) 16
        16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof15.v *)
Admitted.

Lemma exec_alu32_xor_i_0:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.xor (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true)
    (Hl1 : l2 ++
      [encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) EOR_I_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof16.v *)
Admitted.

Lemma exec_alu32_xor_r1:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.xor (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = false)
    (Hhi_0 : Int.eq (decode_arm32 si 0 16) si = true)
    (Hl1 : l2 ++
      [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4)
        (encode_arm32 (int_of_breg dst) EOR_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof16.v *)
Admitted.

Lemma exec_alu32_xor_r2:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.xor (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = false)
    (Hl1 : l2 ++
      [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      mov_int_to_movwt (decode_arm32 si 16 16) IR11 MOVT_OP;
      encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4)
        (encode_arm32 (int_of_breg dst) EOR_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof16.v *)
Admitted.

Lemma exec_alu32_mov_ri1:
  forall (rs0 rs1: regset) (dst: breg) i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hhi_0 : Int.eq (decode_arm32 i 0 16) i = true)
    (Hl1 : l2 ++ [mov_int_to_movwt (decode_arm32 i 0 16) (ireg_of_breg dst) MOVW_OP] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof17.v *)
Admitted.

Lemma exec_alu32_mov_ri2:
  forall (rs0 rs1: regset) (dst: breg) i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hl1 : l2 ++
      [mov_int_to_movwt (decode_arm32 i 0 16) (ireg_of_breg dst) MOVW_OP;
      mov_int_to_movwt (decode_arm32 i 16 16) (ireg_of_breg dst) MOVT_OP] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  (**r see TSSemanticsBproof17.v *)
Admitted.

Lemma exec_alu32_jit_one:
  forall op dst src rs0 m0 rs1 m1 ld_set st_set l1 ld1 st1 jit_blk st_blk
    ars0 astk0 astkb am
  (Hexe_one : exec_alu32 op dst src rs0 m0 = Next rs1 m1)
  (Hjit_one : jit_one op dst src ld_set st_set = Some (l1, ld1, st1))
  (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m0) (AState ars0 astk0 astkb am)),
    exists (ars1 : aregset) (astk1 : astack),
      exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
      match_states jit_blk st_blk ld1 st1 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  unfold exec_alu32, eval_reg_imm, jit_one, nextinstr; intros.
  destruct src as [src | si].
  - destruct jit_call_save_reg as ((l2 & ld_set2) & st_set2) eqn: Hsave.
    unfold eval_alu32, bpf_alu32_to_thumb_reg, bpf_alu32_to_thumb_reg_comm in *; destruct op.
    + destruct Val.add eqn: HALU; inversion Hexe_one; subst; clear Hexe_one.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      injection Hjit_one as Hl1 Hld1 Hst1.
      subst ld1 st1.

      eapply exec_alu32_add_r in HALU; eauto.
    + destruct Val.sub eqn: HALU; inversion Hexe_one; subst; clear Hexe_one.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      injection Hjit_one as Hl1 Hld1 Hst1.
      subst ld1 st1.
      eapply exec_alu32_sub_r in HALU; eauto.
    + destruct Val.mul eqn: HALU; inversion Hexe_one; subst; clear Hexe_one.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      injection Hjit_one as Hl1 Hld1 Hst1.
      subst ld1 st1.
      eapply exec_alu32_mul in HALU; eauto.
    + inversion Hjit_one.
    + destruct Val.or eqn: HALU; inversion Hexe_one; subst; clear Hexe_one.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      injection Hjit_one as Hl1 Hld1 Hst1.
      subst ld1 st1.
      eapply exec_alu32_orr_r in HALU; eauto.
    + destruct Val.and eqn: HALU; inversion Hexe_one; subst; clear Hexe_one.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      injection Hjit_one as Hl1 Hld1 Hst1.
      subst ld1 st1.
      eapply exec_alu32_and_r in HALU; eauto.
    + inversion Hjit_one.
    + inversion Hjit_one.
    + inversion Hjit_one.
    + inversion Hjit_one.
    + destruct Val.xor eqn: HALU; inversion Hexe_one; subst; clear Hexe_one.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      injection Hjit_one as Hl1 Hld1 Hst1.
      subst ld1 st1.
      eapply exec_alu32_xor_r in HALU; eauto.
    + destruct (rs0 src) eqn: HALU; inversion Hexe_one; subst; clear Hexe_one.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      destruct reg_ireg_eqb eqn: HREG_EQ;
        [ apply reg_ireg_eqb_ireg_of_breg_true in HREG_EQ |
          apply reg_ireg_eqb_ireg_of_breg_false in HREG_EQ
        ].
      * rewrite app_nil_r in Hjit_one.
        subst dst.

        injection Hjit_one as Hl1 Hld1 Hst1.
        subst l1 ld1 st1.
        eapply exec_alu32_mov_r1 in HALU; eauto.
      * injection Hjit_one as Hl1 Hld1 Hst1.
        subst ld1 st1.
        eapply exec_alu32_mov_r in HALU; eauto.
    + inversion Hjit_one.
  - destruct jit_call_save_imm as ((l2 & ld_set2) & st_set2) eqn: Hsave.
    unfold eval_alu32, bpf_alu32_to_thumb_imm,
      bpf_alu32_to_thumb_imm_comm, bpf_alu32_to_thumb_imm_shift_comm in *; destruct op.
    + destruct Val.add eqn: HALU; inversion Hexe_one; subst; clear Hexe_one.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      destruct (Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255)) eqn: Hle_255.
      * injection Hjit_one as Hl1 Hld1 Hst1.
        subst ld1 st1.
        eapply exec_alu32_add_i_0 in HALU; eauto.
      * destruct Int.eq eqn: Hhi_0 in Hjit_one.
        { simpl in Hjit_one.
          injection Hjit_one as Hl1 Hld1 Hst1.
          subst ld1 st1.
          eapply exec_alu32_add_r1 in HALU; eauto.
        }
        { simpl in Hjit_one.
          injection Hjit_one as Hl1 Hld1 Hst1.
          subst ld1 st1.
          eapply exec_alu32_add_r2 in HALU; eauto.
        }
    + destruct Val.sub eqn: HALU; inversion Hexe_one; subst; clear Hexe_one.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      destruct (Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255)) eqn: Hle_255.
      * injection Hjit_one as Hl1 Hld1 Hst1.
        subst ld1 st1.
        eapply exec_alu32_sub_i_0 in HALU; eauto.
      * destruct Int.eq eqn: Hhi_0 in Hjit_one.
        { simpl in Hjit_one.
          unfold bpf_alu32_to_thumb_reg_comm in Hjit_one.
          injection Hjit_one as Hl1 Hld1 Hst1.
          subst ld1 st1.
          eapply exec_alu32_sub_r1 in HALU; eauto.
        }
        { simpl in Hjit_one.
          unfold bpf_alu32_to_thumb_reg_comm in Hjit_one.
          injection Hjit_one as Hl1 Hld1 Hst1.
          subst ld1 st1.
          eapply exec_alu32_sub_r2 in HALU; eauto.
        }
    + destruct Val.mul eqn: HALU; inversion Hexe_one; subst; clear Hexe_one.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      destruct Int.eq eqn: Hhi_0 in Hjit_one.
      * simpl in Hjit_one.
        injection Hjit_one as Hl1 Hld1 Hst1.
        subst ld1 st1.
        eapply exec_alu32_mul_r1 in HALU; eauto.
      * simpl in Hjit_one.
        injection Hjit_one as Hl1 Hld1 Hst1.
        subst ld1 st1.
        eapply exec_alu32_mul_r2 in HALU; eauto.
    + destruct Val.divu eqn: HALU; [| inversion Hexe_one].
      destruct v; inversion Hexe_one; subst; clear Hexe_one.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      destruct Int.eq eqn: Hzero_0 in Hjit_one; [inversion Hjit_one | ].
      destruct Int.eq eqn: Hhi_0 in Hjit_one.
      * simpl in Hjit_one.
        injection Hjit_one as Hl1 Hld1 Hst1.
        subst ld1 st1.
        eapply exec_alu32_div_r1 in HALU; eauto.
      * simpl in Hjit_one.
        injection Hjit_one as Hl1 Hld1 Hst1.
        subst ld1 st1.
        eapply exec_alu32_div_r2 in HALU; eauto.

    + destruct Val.or eqn: HALU; inversion Hexe_one; subst; clear Hexe_one.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      destruct (Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255)) eqn: Hle_255.
      * injection Hjit_one as Hl1 Hld1 Hst1.
        subst ld1 st1.
        eapply exec_alu32_orr_i_0 in HALU; eauto.
      * destruct Int.eq eqn: Hhi_0 in Hjit_one.
        { simpl in Hjit_one.
          unfold bpf_alu32_to_thumb_reg_comm in Hjit_one.
          injection Hjit_one as Hl1 Hld1 Hst1.
          subst ld1 st1.
          eapply exec_alu32_orr_r1 in HALU; eauto.
        }
        { simpl in Hjit_one.
          unfold bpf_alu32_to_thumb_reg_comm in Hjit_one.
          injection Hjit_one as Hl1 Hld1 Hst1.
          subst ld1 st1.
          eapply exec_alu32_orr_r2 in HALU; eauto.
        }
    + destruct Val.and eqn: HALU; inversion Hexe_one; subst; clear Hexe_one.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      destruct (Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255)) eqn: Hle_255.
      * injection Hjit_one as Hl1 Hld1 Hst1.
        subst ld1 st1.
        eapply exec_alu32_and_i_0 in HALU; eauto.
      * destruct Int.eq eqn: Hhi_0 in Hjit_one.
        { simpl in Hjit_one.
          unfold bpf_alu32_to_thumb_reg_comm in Hjit_one.
          injection Hjit_one as Hl1 Hld1 Hst1.
          subst ld1 st1.
          eapply exec_alu32_and_r1 in HALU; eauto.
        }
        { simpl in Hjit_one.
          unfold bpf_alu32_to_thumb_reg_comm in Hjit_one.
          injection Hjit_one as Hl1 Hld1 Hst1.
          subst ld1 st1.
          eapply exec_alu32_and_r2 in HALU; eauto.
        }
    + destruct Val.shl eqn: HALU; inversion Hexe_one; subst; clear Hexe_one.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      destruct (Int.cmpu Cle Int.zero si && Int.cmpu Clt si (Int.repr 32)) eqn: Hlt_32;
        [| inversion Hjit_one].
      simpl in Hjit_one.
      injection Hjit_one as Hl1 Hld1 Hst1.
      subst ld1 st1.
      eapply exec_alu32_lsl_r1 in HALU; eauto.
    + destruct Val.shru eqn: HALU; inversion Hexe_one; subst; clear Hexe_one.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      destruct (Int.cmpu Cle Int.zero si && Int.cmpu Clt si (Int.repr 32)) eqn: Hlt_32;
        [| inversion Hjit_one].
      simpl in Hjit_one.
      injection Hjit_one as Hl1 Hld1 Hst1.
      subst ld1 st1.
      eapply exec_alu32_lsr_r1 in HALU; eauto.
    + destruct Val.neg eqn: HALU; inversion Hexe_one; subst; clear Hexe_one.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      destruct Int.eq eqn: Hhi_0 in Hjit_one.
      * simpl in Hjit_one.
        injection Hjit_one as Hl1 Hld1 Hst1.
        subst ld1 st1.
        eapply exec_alu32_neg_r1 in HALU; eauto.
      * simpl in Hjit_one.
        injection Hjit_one as Hl1 Hld1 Hst1.
        subst ld1 st1.
        eapply exec_alu32_neg_r2 in HALU; eauto.
    + inversion Hjit_one.

    + destruct Val.xor eqn: HALU; inversion Hexe_one; subst; clear Hexe_one.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      destruct (Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255)) eqn: Hle_255.
      * injection Hjit_one as Hl1 Hld1 Hst1.
        subst ld1 st1.
        eapply exec_alu32_xor_i_0 in HALU; eauto.
      * destruct Int.eq eqn: Hhi_0 in Hjit_one.
        { simpl in Hjit_one.
          unfold bpf_alu32_to_thumb_reg_comm in Hjit_one.
          injection Hjit_one as Hl1 Hld1 Hst1.
          subst ld1 st1.
          eapply exec_alu32_xor_r1 in HALU; eauto.
        }
        { simpl in Hjit_one.
          unfold bpf_alu32_to_thumb_reg_comm in Hjit_one.
          injection Hjit_one as Hl1 Hld1 Hst1.
          subst ld1 st1.
          eapply exec_alu32_xor_r2 in HALU; eauto.
        }
    + inversion Hexe_one; subst; clear Hexe_one.
      rename si into i.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      destruct Int.eq eqn: Hhi_0 in Hjit_one.
      * simpl in Hjit_one.
        injection Hjit_one as Hl1 Hld1 Hst1.
        subst ld1 st1.
        eapply exec_alu32_mov_ri1 in Hsave; eauto.
      * simpl in Hjit_one.
        injection Hjit_one as Hl1 Hld1 Hst1.
        subst ld1 st1.
        eapply exec_alu32_mov_ri2 in Hsave; eauto.

    + destruct Val.shr eqn: HALU; inversion Hexe_one; subst; clear Hexe_one.
      remember (BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
          (BPregmap.set dst (Vint i) rs0)) as rs1 eqn: Hrs1.

      destruct (Int.cmpu Cle Int.zero si && Int.cmpu Clt si (Int.repr 32)) eqn: Hlt_32;
        [| inversion Hjit_one].
      simpl in Hjit_one.
      injection Hjit_one as Hl1 Hld1 Hst1.
      subst ld1 st1.
      eapply exec_alu32_asr_r1 in HALU; eauto.
Qed.

Lemma exec_alu32_list_jit_pc:
  forall (l: bin_code) rs m jit_blk st_blk ld_set st_set ars1 astk1 astkb1 am1 v k
    (HPC : jit_alu32_thumb_pc k = Some l)
    (HST_PC: Mem.load Mint32 am1 st_blk 44%Z = Some (Vint v) /\
      Val.add (Vint v) (Vint (Int.repr (Z.of_nat k))) = rs#BPC)
    (HST: match_states jit_blk st_blk ld_set st_set (State rs m) (AState ars1 astk1 astkb1 am1)),
      exists ars2 astk2 am2,
        exec_bin_list l ars1 astk1 astkb1 am1 = ANext ars2 astk2 astkb1 am2 /\
        match_states jit_blk st_blk ld_set st_set (State rs m) (AState ars2 astk2 astkb1 am2) /\
        (Mem.load Mint32 am2 st_blk 44%Z = Some (rs#BPC)) /\
        (exists v_pc, ars2#IR11 = Cval (Vint v_pc)).
Proof.
  intros.
  unfold jit_alu32_thumb_pc in HPC.
  unfold jit_alu32_thumb_pc_add in HPC.
  destruct (_ && _) eqn: Hle_255; [| inversion HPC].
  injection HPC as HPC.
  unfold jit_alu32_thumb_mem_template_jit in HPC.
  subst l.
  simpl.
  rewrite decode_ldr_i_12_11.
  simpl.
  inversion HST; subst.
  rewrite HIR12.
  unfold aexec_load; simpl.
  rewrite Ptrofs.add_zero_l.
  replace (Ptrofs.unsigned (Ptrofs.of_int (Int.repr 44))) with 44%Z by reflexivity.
  destruct HST_PC as (HST_PC1 & HST_PC2).
  rewrite HST_PC1.
  rewrite decode_add_i_11; auto.
  simpl.
  rewrite decode_str_i_12_11.
  simpl.
  unfold anextinstr.
  unfold aexec_store, aexec_store'; simpl.
  unfold anextinstr_nf, anextinstr, aundef_flags; simpl. repeat abreg_solver_error_prone.
  rewrite HIR12.
  simpl.

  assert (Heq: is_final_state ars1 = false). {
    unfold is_final_state.
    assert (Heq: aval_eq (ars1 IR13) (Aval (Rval (Sreg IR13))) = false).
    - rewrite HIR13.
      simpl.
      auto.
    - rewrite Heq.
      rewrite andb_false_r.
      rewrite andb_false_l.
      auto.
  }
  rewrite Heq; clear Heq.

  assert (Heq: is_final_state ((ars1 # IR11 <- (Cval (Vint v))) # PC <-
      (aoffset_ptr (ars1 PC) wsize)) = false). {
    unfold is_final_state.
    assert (Heq: aval_eq (((ars1 # IR11 <- (Cval (Vint v))) # PC <-
      (aoffset_ptr (ars1 PC) wsize)) IR13) (Aval (Rval (Sreg IR13))) = false).
    - repeat abreg_solver_error_prone.
      rewrite Pregmap.gso. 2:{ intro HF; inversion HF. }
      rewrite HIR13.
      simpl.
      auto.
    - rewrite Heq.
      rewrite andb_false_r.
      rewrite andb_false_l.
      auto.
  }
  rewrite Heq; clear Heq.

  assert (Heq: is_final_state ((fun r : PregEq.t =>
       match r with
       | CR _ => Cval Vundef
       | _ =>
           ((ars1 # IR11 <- (Cval (Vint v)))
            # PC <- (aoffset_ptr (ars1 PC) wsize))
           # IR11 <-
           (Cval
              (Vint
                 (Int.add v
                    (Int.repr (Z.of_nat k))))) r
       end) # PC <-
      (aoffset_ptr (aoffset_ptr (ars1 PC) wsize)
         wsize)) = false). {
    unfold is_final_state.
    assert (Heq: aval_eq (((fun r : PregEq.t =>
       match r with
       | CR _ => Cval Vundef
       | _ =>
           ((ars1 # IR11 <- (Cval (Vint v)))
            # PC <- (aoffset_ptr (ars1 PC) wsize))
           # IR11 <-
           (Cval
              (Vint
                 (Int.add v
                    (Int.repr (Z.of_nat k))))) r
       end) # PC <-
      (aoffset_ptr (aoffset_ptr (ars1 PC) wsize)
         wsize)) IR13) (Aval (Rval (Sreg IR13))) = false).
    - repeat abreg_solver_error_prone.
      rewrite Pregmap.gso. 2:{ intro HF; inversion HF. }
      repeat abreg_solver_error_prone.
      rewrite Pregmap.gso. 2:{ intro HF; inversion HF. }
      rewrite HIR13.
      simpl.
      auto.
    - rewrite Heq.
      rewrite andb_false_r.
      rewrite andb_false_l.
      auto.
  }
  rewrite Heq; clear Heq.
  

  destruct BLK as (BLK1 & BLK2).
  unfold eq_block.
  destruct peq. { exfalso. apply BLK2. assumption. }
  rewrite Ptrofs.add_zero_l.
  replace (Ptrofs.unsigned (Ptrofs.of_int (Int.repr 44))) with 44%Z by reflexivity.

  assert (Heq: Mem.valid_access am1 Mint32 st_blk 44 Writable). {
    clear - HPERM.
    unfold Mem.range_perm in HPERM.
    unfold Mem.valid_access.
    split; [| unfold align_chunk;
      replace 44%Z with (11*4)%Z by reflexivity; apply Z.divide_factor_r].
    unfold size_chunk, Mem.range_perm.
    intros.
    apply HPERM.
    unfold state_block_size. lia.
  }

  eapply Mem.valid_access_store in Heq; eauto.
  destruct Heq as (m2 & Hm2_eq).
  rewrite Hm2_eq.
  repeat abreg_solver_error_prone.

    assert (Heq: is_final_state (((fun r : PregEq.t =>
        match r with
        | CR _ => Cval Vundef
        | _ =>
            ((ars1 # IR11 <- (Cval (Vint v)))
             # PC <-
             (aoffset_ptr (ars1 PC) wsize))
            # IR11 <-
            (Cval
               (Vint
                  (Int.add v
                     (Int.repr (Z.of_nat k))))) r
        end) # PC <-
       (aoffset_ptr (aoffset_ptr (ars1 PC) wsize)
          wsize)) # PC <-
      (aoffset_ptr
         (aoffset_ptr
            (aoffset_ptr (ars1 PC) wsize) wsize)
         wsize)) = false). {
      unfold is_final_state.
      assert (Heq: aval_eq ((((fun r : PregEq.t =>
        match r with
        | CR _ => Cval Vundef
        | _ =>
            ((ars1 # IR11 <- (Cval (Vint v)))
             # PC <-
             (aoffset_ptr (ars1 PC) wsize))
            # IR11 <-
            (Cval
               (Vint
                  (Int.add v
                     (Int.repr (Z.of_nat k))))) r
        end) # PC <-
       (aoffset_ptr (aoffset_ptr (ars1 PC) wsize)
          wsize)) # PC <-
      (aoffset_ptr
         (aoffset_ptr
            (aoffset_ptr (ars1 PC) wsize) wsize)
         wsize)) IR13)
        (Aval (Rval (Sreg IR13))) = false).
      - repeat abreg_solver_error_prone.
        rewrite Pregmap.gso. 2:{ intro HF; inversion HF. }
        repeat abreg_solver_error_prone.
        rewrite Pregmap.gso. 2:{ intro HF; inversion HF. }
        rewrite HIR13.
        simpl.
        auto.
      - rewrite Heq.
        rewrite andb_false_r.
        rewrite andb_false_l.
        auto.
    }
    rewrite Heq; clear Heq.


  eexists; eexists; eexists.
  split; [reflexivity | ].
  split.
  - constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; repeat abreg_solver.
    + intros.
      specialize (Hfloat _ H).
      repeat float_preg_of_solver.
      repeat (destruct H as [H | H];
          [subst x; auto|]); inversion H.
    + unfold Mem.range_perm in *.
      intros.
      specialize (HPERM _ H).
      eapply Mem.perm_store_1; eauto.
    + rewrite <- HAR11.
      unfold astack_load.
      destruct Mem.valid_access_dec as [HT| HF].
      * eapply Mem.store_valid_access_2 in HT; eauto.
        destruct Mem.valid_access_dec as [HT1| HF1].
        { f_equal. } exfalso. apply HF1. auto.
      * destruct Mem.valid_access_dec as [HT1| HF1].
        { exfalso. apply HF.
          eapply Mem.store_valid_access_1; eauto.
        }
        reflexivity.

    + destruct HIRPC as (va_pc & HIRPC).
      unfold aoffset_ptr.
      repeat abreg_solver_error_prone.
      rewrite HIRPC.
      simpl.
      eexists; f_equal.

    + unfold match_regs in *.
      intros.
      specialize (REG r).
      destruct REG as (REG1 & REG2 & REG3).
      split.
      { intro Hin. specialize (REG1 Hin).
        destruct REG1 as (vr & Hrs_eq & Hars_eq).
        exists vr.
        split; [auto | ].
        repeat abreg_solver.
      }
      split.
      { intro Hin. specialize (REG2 Hin).
        repeat abreg_solver.
      }
      intro Hin. specialize (REG3 Hin).
      destruct REG3 as (vr & Hrs_eq & Hars_eq).
      exists vr.
      split; [auto | ].
      rewrite <- Hars_eq.
      eapply Mem.load_store_other; eauto.
      right. left. simpl. destruct r; simpl; lia.
    + unfold match_stack in *.
      destruct STK as (INIT_STK & STK).
      split.
      {
        unfold init_arm_stack in *.
        destruct INIT_STK as (INIT_STK1 & INIT_STK2).
        split.
        - rewrite <- INIT_STK1.
          unfold astack_load.
          destruct Mem.valid_access_dec as [HT| HF].
          * eapply Mem.store_valid_access_2 in HT; eauto.
            destruct Mem.valid_access_dec as [HT1| HF1].
            { f_equal. } exfalso. apply HF1. auto.
          * destruct Mem.valid_access_dec as [HT1| HF1].
            { exfalso. apply HF.
              eapply Mem.store_valid_access_1; eauto.
            }
            reflexivity.
        - unfold Mem.range_perm in *.
          intros.
          specialize (INIT_STK2 _ H).
          eapply Mem.perm_store_1; eauto.
      }
      intros.
      specialize (STK _ H).
      destruct STK as (STK1 & STK2).
      split.
      {
        intros.
        rewrite <- STK1; auto.
        unfold astack_load.
        destruct Mem.valid_access_dec as [HT| HF].
        * eapply Mem.store_valid_access_2 in HT; eauto.
          destruct Mem.valid_access_dec as [HT1| HF1].
          { f_equal. } exfalso. apply HF1. auto.
        * destruct Mem.valid_access_dec as [HT1| HF1].
          { exfalso. apply HF.
            eapply Mem.store_valid_access_1; eauto.
          }
          reflexivity.
      }
      intros.
      rewrite <- STK2; auto.
      repeat abreg_solver.
    + unfold match_memory in *.
      eapply store_unchanged_on_3; eauto.
      intros.
      intro HF.
      destruct HF as (HF & _).
(*
      destruct HF as (_ & HF & _). *)
      apply HF; reflexivity.
  - split.
    + unfold Val.add in HST_PC2.
      rewrite <- HST_PC2.
      erewrite Mem.load_store_same; eauto.
      unfold Val.load_result; f_equal.
    + repeat abreg_solver_error_prone.
      eexists; auto.
Qed.

Lemma exec_bin_list_jit_store:
  forall st_set ld_set jit_blk st_blk rs m (ars1: aregset) astk1 astkb1 am1 v_pc
    (Hir11: ars1#IR11 = Cval (Vint v_pc))
    (Hst2 : match_states jit_blk st_blk ld_set st_set (State rs m) (AState ars1 astk1 astkb1 am1))
    (Hpc2 : Mem.load Mint32 am1 st_blk 44 = Some (rs BPC)),
      exists ars2 am2,
        exec_bin_list (jit_alu32_thumb_store st_set) ars1 astk1 astkb1 am1 =
          ANext ars2 astk1 astkb1 am2 /\
        match_states jit_blk st_blk ld_set [] (State rs m) (AState ars2 astk1 astkb1 am2) /\
        ars2 IR11 = Cval (Vint v_pc) /\
        Mem.load Mint32 am2 st_blk 44 = Some (rs BPC).
Proof.
  induction st_set; simpl; intros.
  - eexists; eexists.
    destruct is_final_state; split; eauto.
  - unfold jit_alu32_thumb_mem_template_jit.
    rewrite decode_str_i_12.
    simpl.
    inversion Hst2; subst.
    rewrite HIR12.
    simpl.
    rewrite Ptrofs.add_zero_l.
    unfold aexec_store, aexec_store'; simpl.
    destruct BLK as (BLK1 & BLK2).
    unfold eq_block.
    destruct peq. { exfalso. apply BLK2. assumption. }

    unfold match_regs in REG.
    specialize (REG a) as REG_a.
    destruct REG_a as (REG_a & _).
    assert (Heq: In a (set_union breg_eq ld_set (a :: st_set))). {
      apply set_union_intro2.
      simpl.
      auto.
    }
    specialize (REG_a Heq); clear Heq.
    destruct REG_a as (vr_a & Ha1 & Ha2).
    rewrite Ha2. rewrite ptr_int_mul_4.


    assert (Heq: is_final_state ars1 = false). {
      unfold is_final_state.
      assert (Heq: aval_eq (ars1 IR13) (Aval (Rval (Sreg IR13))) = false).
      - rewrite HIR13.
        simpl.
        auto.
      - rewrite Heq.
        rewrite andb_false_r.
        rewrite andb_false_l.
        auto.
    }
    rewrite Heq; clear Heq.


    assert (Heq: Mem.valid_access am1 Mint32 st_blk (z_of_breg a * 4) Writable). {
      clear - HPERM.
      unfold Mem.range_perm in HPERM.
      unfold Mem.valid_access.
      split; [| unfold align_chunk; apply Z.divide_factor_r].
      unfold size_chunk, Mem.range_perm.
      intros.
      apply HPERM.
      unfold state_block_size. destruct a; simpl in H; lia.
    }

    eapply Mem.valid_access_store in Heq; eauto.
    destruct Heq as (m2 & Hm2_eq).
    rewrite Hm2_eq.
    eapply IHst_set; eauto.

    2:{ rewrite <- Hpc2. erewrite Mem.load_store_other; eauto.
      right. right. simpl. destruct a; simpl; lia. }

    constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; repeat abreg_solver.
    + intros.
      specialize (Hfloat _ H).
      repeat float_preg_of_solver.
      repeat (destruct H as [H | H];
          [subst x; auto|]); inversion H.
    + unfold Mem.range_perm in *.
      intros.
      specialize (HPERM _ H).
      eapply Mem.perm_store_1; eauto.
    + destruct HNoDup as (HNoDup1 & HNoDup2);
      split; auto.
      apply NoDup_cons_iff in HNoDup2.
      destruct HNoDup2 as (_ & HF); auto.
    + rewrite <- HAR11.
      unfold astack_load.
      destruct Mem.valid_access_dec as [HT| HF].
      * eapply Mem.store_valid_access_2 in HT; eauto.
        destruct Mem.valid_access_dec as [HT1| HF1].
        { f_equal. } exfalso. apply HF1. auto.
      * destruct Mem.valid_access_dec as [HT1| HF1].
        { exfalso. apply HF.
          eapply Mem.store_valid_access_1; eauto.
        }
        reflexivity.

    + destruct HIRPC as (va_pc & HIRPC).
      unfold aoffset_ptr.
      repeat abreg_solver_error_prone.
      rewrite HIRPC.
      simpl.
      eexists; f_equal.

    + intros.
      apply HSUB. right. auto.
    + unfold match_regs.
      intros.
      specialize (REG r).
      destruct REG as (REG1 & REG2 & REG3).
      split.
      { intro Hin.
        assert (Heq: In r (set_union breg_eq ld_set (a :: st_set))). {
          apply set_union_elim in Hin.
          destruct Hin as [Hin | Hin].
          - apply set_union_intro1; auto.
          - apply set_union_intro2. right; auto.
        }
        specialize (REG1 Heq); clear Heq.
        destruct REG1 as (vr & Hrs_eq & Hars_eq).
        exists vr.
        split; [auto | ].
        repeat abreg_solver.
      }
      split.
      { intro Hin. destruct Hin as (Hin & Hin1).
        destruct (breg_eq r a) as [Hr_eq | Hr_neq].
        - subst r.
          exfalso.
          apply Hin.
          apply set_union_intro1. apply HSUB. simpl; auto.
        -
          assert (Heq: ~ In r (set_union breg_eq ld_set (a :: st_set))
           /\ In r rbpf_arm_callee_save). {
            split; auto.
            intro HF. apply Hin.
            apply set_union_elim in HF.
            destruct HF as [HF | HF].
            - apply set_union_intro1; auto.
            - destruct HF as [HF | HF].
              + exfalso; apply Hr_neq; auto.
              + apply set_union_intro2; auto.
          }
        specialize (REG2 Heq); clear Heq.
        repeat abreg_solver.
      }
      {
        intro Hin.
        destruct (breg_eq r a) as [Hr_eq | Hr_neq].
        - subst r.
          exists vr_a.
          split; auto.
          erewrite Mem.load_store_same; eauto. unfold Val.load_result; simpl; auto.
        -
          assert (Heq: ~ In r (a :: st_set)). {
            intro HF. apply Hin.
            destruct HF as [HF | HF].
            - exfalso; apply Hr_neq; auto.
            - auto.
          }
        specialize (REG3 Heq); clear Heq.
        destruct REG3 as (vr & Hrs_eq & Hars_eq).
        exists vr.
        split; [auto | ].
        rewrite <- Hars_eq.
        eapply Mem.load_store_other; eauto.
        right. simpl. destruct r; destruct a; simpl; try lia; try (exfalso; apply Hr_neq; reflexivity).
      }
    + unfold match_stack in *.
      destruct STK as (INIT_STK & STK).
      split.
      {
        unfold init_arm_stack in *.
        destruct INIT_STK as (INIT_STK1 & INIT_STK2).
        split.
        - rewrite <- INIT_STK1.
          unfold astack_load.
          destruct Mem.valid_access_dec as [HT| HF].
          * eapply Mem.store_valid_access_2 in HT; eauto.
            destruct Mem.valid_access_dec as [HT1| HF1].
            { f_equal. } exfalso. apply HF1. auto.
          * destruct Mem.valid_access_dec as [HT1| HF1].
            { exfalso. apply HF.
              eapply Mem.store_valid_access_1; eauto.
            }
            reflexivity.
        - unfold Mem.range_perm in *.
          intros.
          specialize (INIT_STK2 _ H).
          eapply Mem.perm_store_1; eauto.
      }
      intros.
      specialize (STK _ H).
      destruct STK as (STK1 & STK2).
      split.
      {
        intros.
        rewrite <- STK1; auto.
        - unfold astack_load.
          destruct Mem.valid_access_dec as [HT| HF].
          + eapply Mem.store_valid_access_2 in HT; eauto.
            destruct Mem.valid_access_dec as [HT1| HF1].
            { f_equal. } exfalso. apply HF1. auto.
          + destruct Mem.valid_access_dec as [HT1| HF1].
            { exfalso. apply HF.
              eapply Mem.store_valid_access_1; eauto.
            }
            reflexivity.
        - apply set_union_elim in H0.
          destruct H0 as [HT | HT].
          + apply set_union_intro1; auto.
          + apply set_union_intro2; right; auto.
      }
      {
        destruct (breg_eq r a) as [Hr_eq | Hr_neq].
        - subst r.
          intros.
          exfalso. apply H0. apply set_union_intro1. apply HSUB. simpl; auto.
        - intros.
          rewrite <- STK2; auto.
          destruct H0 as (H0 & H1).
          split; auto.
          intro HF.
          apply H0.
          apply set_union_elim in HF.
          destruct HF as [HF | HF].
          + apply set_union_intro1; auto.
          + simpl in HF.
            destruct HF as [HF | HF].
            * exfalso; apply Hr_neq; auto.
            * apply set_union_intro2; auto.
      }
    + unfold match_memory in *.
      eapply store_unchanged_on_3; eauto.
      intros.
      intro HF. (*
      destruct HF as (_ & HF & _).*) destruct HF as (HF & _).
      apply HF; reflexivity.
Qed.

Lemma exec_bin_list_jit_reset_11:
  forall ld_set jit_blk st_blk rs m (ars1: aregset) astk1 astkb1 am1
    (Hst3 : match_states jit_blk st_blk ld_set [] (State rs m) (AState ars1 astk1 astkb1 am1)),
      exists ars2,
        exec_bin_list [jit_alu32_thumb_mem_template_jit LDR_I_OP (Int.repr 11) (int_of_ireg IR13) (Int.repr 44)] ars1 astk1 astkb1 am1 =
          ANext ars2 astk1 astkb1 am1 /\
        match_states jit_blk st_blk ld_set [] (State rs m) (AState ars2 astk1 astkb1 am1) /\
        (ars2#IR11 = Aval (Rval (Sreg IR11))).
Proof.
  intros.
  unfold jit_alu32_thumb_mem_template_jit.
  simpl.
  rewrite decode_ldr_i_13_11.
  simpl.
  inversion Hst3; subst.
  rewrite HIR13.
  simpl.
  rewrite Ptrofs.add_zero_l.
  replace (Ptrofs.unsigned (Ptrofs.of_int (Int.repr 44))) with 44%Z by reflexivity.
  rewrite HAR11.

    assert (Heq: is_final_state ars1 = false). {
      unfold is_final_state.
      assert (Heq: aval_eq (ars1 IR13) (Aval (Rval (Sreg IR13))) = false).
      - rewrite HIR13.
        simpl.
        auto.
      - rewrite Heq.
        rewrite andb_false_r.
        rewrite andb_false_l.
        auto.
    }
    rewrite Heq; clear Heq.

    assert (Heq: is_final_state (anextinstr true
         ars1 # IR11 <- (Aval (Rval (Sreg IR11)))) = false). {
      unfold is_final_state.
      assert (Heq: aval_eq ((anextinstr true
         ars1 # IR11 <- (Aval (Rval (Sreg IR11)))) IR13) (Aval (Rval (Sreg IR13))) = false).
      - unfold anextinstr.
        repeat abreg_solver_error_prone.
        rewrite Pregmap.gso. 2:{ intro HF; inversion HF. }
        rewrite HIR13.
        simpl.
        auto.
      - rewrite Heq.
        rewrite andb_false_r.
        rewrite andb_false_l.
        auto.
    }
    rewrite Heq; clear Heq.


  eexists.
  split; eauto.
  split.
  - constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; repeat abreg_solver.
    + intros.
      specialize (Hfloat _ H).
      repeat float_preg_of_solver.
      repeat (destruct H as [H | H];
          [subst x; auto|]); inversion H.

    + destruct HIRPC as (va_pc & HIRPC).
      unfold aoffset_ptr.
      repeat abreg_solver_error_prone.
      rewrite Pregmap.gso. 2:{ intro HF; inversion HF. }
      rewrite HIRPC.
      simpl.
      eexists; f_equal.

    + unfold match_regs in *.
      intros.
      specialize (REG r).
      destruct REG as (REG1 & REG2 & REG3).
      split.
      { intro Hin.
        specialize (REG1 Hin).
        destruct REG1 as (vr & Hrs_eq & Hars_eq).
        exists vr.
        split; [auto | ].
        repeat abreg_solver.
      }
      split.
      { intro Hin.
        specialize (REG2 Hin).
        repeat abreg_solver.
      }
      {
        intro Hin.
        specialize (REG3 Hin).
        destruct REG3 as (vr & Hrs_eq & Hars_eq).
        exists vr.
        split; auto.
      }
    + unfold match_stack in *.
      destruct STK as (INIT_STK & STK).
      split; auto.

      intros.
      specialize (STK _ H).
      destruct STK as (STK1 & STK2).
      split.
      {
        intros.
        rewrite <- STK1; auto.
      }
      { intros.
        rewrite <- STK2; auto.
        repeat abreg_solver.
      }
  - unfold anextinstr, aundef_flags; repeat abreg_solver.
    rewrite Pregmap.gss. reflexivity.
Qed.

Lemma exec_bin_list_jit_reset:
  forall ld_set jit_blk st_blk rs m (ars1: aregset) astk1 astkb1 am1
    (Hir11: ars1 IR11 = Aval (Rval (Sreg IR11)))
    (Hst3 : match_states jit_blk st_blk ld_set [] (State rs m) (AState ars1 astk1 astkb1 am1)),
      exists ars2,
        exec_bin_list (jit_alu32_thumb_reset1 ld_set) ars1 astk1 astkb1 am1 =
          ANext ars2 astk1 astkb1 am1 /\
        match_states jit_blk st_blk [] [] (State rs m) (AState ars2 astk1 astkb1 am1) /\
        ars2 IR11 = Aval (Rval (Sreg IR11)).
Proof.
  induction ld_set; simpl; intros.
  - exists ars1. destruct is_final_state; split; auto.
  - unfold jit_alu32_thumb_mem_template_jit.
    destruct (_ && _) eqn: Hcallee.
    2:{ eapply IHld_set; eauto.
      inversion Hst3; subst.
      constructor; auto.
      - destruct HNoDup as (HNoDup1 & HNoDup2).
        split; auto.
        apply NoDup_cons_iff in HNoDup1.
        destruct HNoDup1 as (_ & HNoDup1); auto.
      - intros.
        inversion H.
      - unfold match_regs in *.
        intros.
        specialize (REG r).
        destruct REG as (REG1 & REG2 & REG3).
        split.
        + intros.
          apply REG1.
          apply set_union_elim in H.
          destruct H as [HT |HT]; [| inversion HT].
          apply set_union_intro1; simpl; auto.
        + split; intros.
          { destruct (breg_eq r a) as [Hr_eq | Hr_neq].
            - subst r.
              exfalso.
              destruct H as (_ & HF).
              clear - Hcallee HF.
              apply andb_false_iff in Hcallee.
              destruct Hcallee as [Hle | Hle];
                apply negb_true_iff in Hle;
                eapply LemmaInt.Cle_Zle_unsigned in Hle; eauto;
                rewrite int_unsigned_repr_int in Hle.
              + replace (Int.unsigned (Int.repr 3)) with 3%Z in Hle by reflexivity.
                destruct a; simpl in Hle; try lia.
                all: simpl in HF; repeat (destruct HF as [HF | HF]; [inversion HF |]);
                  inversion HF.
              + replace (Int.unsigned (Int.repr 11)) with 11%Z in Hle by reflexivity.
                destruct a; simpl in Hle; lia.
            - apply REG2. destruct H as (H & H1).
              split; auto.
              intro HF. apply H.
              apply set_union_elim in HF.
              destruct HF as [HF | HF]; [| inversion HF].
              destruct HF as [HF | HF].
              + exfalso; apply Hr_neq; auto.
              + apply set_union_intro1; auto.
          }
          apply REG3; auto.
      - unfold match_stack in *.
        destruct STK as (INIT_STK & STK).
        split; auto.
        intros.
        specialize (STK r H).
        destruct STK as (STK1 & STK2).
        split.
        + intros. apply STK1.
          apply set_union_elim in H0.
          destruct H0 as [HF | HF]; [| inversion HF].
          apply set_union_intro1. right; auto.
        + intros.
          { destruct (breg_eq r a) as [Hr_eq | Hr_neq].
            - subst r.
              exfalso.
              destruct H0 as (_ & HF).
              clear - Hcallee HF.
              apply andb_false_iff in Hcallee.
              destruct Hcallee as [Hle | Hle];
                apply negb_true_iff in Hle;
                eapply LemmaInt.Cle_Zle_unsigned in Hle; eauto;
                rewrite int_unsigned_repr_int in Hle.
              + replace (Int.unsigned (Int.repr 3)) with 3%Z in Hle by reflexivity.
                destruct a; simpl in Hle; try lia.
                all: simpl in HF; repeat (destruct HF as [HF | HF]; [inversion HF |]);
                  inversion HF.
              + replace (Int.unsigned (Int.repr 11)) with 11%Z in Hle by reflexivity.
                destruct a; simpl in Hle; lia.
            - apply STK2. destruct H0 as (H0 & H1).
              split; auto.
              intro HF. apply H0.
              apply set_union_elim in HF.
              destruct HF as [HF | HF]; [| inversion HF].
              destruct HF as [HF | HF].
              + exfalso; apply Hr_neq; auto.
              + apply set_union_intro1; auto.
          }
    }

    assert (Heq: exists ars2 : aregset,
      exec_bin_list
        [encode_arm32 (encode_arm32 (int_of_breg a) (Int.mul (int_of_breg a) (Int.repr 4)) 12 4)
           (encode_arm32 (int_of_ireg IR13) LDR_I_OP 0 4) 16 16]
        ars1 astk1 astkb1 am1 = ANext ars2 astk1 astkb1 am1 /\
      match_states jit_blk st_blk ld_set [] (State rs m) (AState ars2 astk1 astkb1 am1) /\
      ars2 IR11 = Aval (Rval (Sreg IR11))). {
      simpl.
      rewrite decode_ldr_i_13.
      simpl.
      inversion Hst3; subst.
      rewrite HIR13.
      simpl.
      rewrite Ptrofs.add_zero_l.
      rewrite ptr_int_mul_4.
      unfold match_stack in STK.
      destruct STK as (INIT_STK & STK).
      assert (Heq: In a rbpf_arm_callee_save). {
        clear - Hcallee.
        rewrite andb_true_iff in Hcallee.
        destruct Hcallee as (H1 & H2).
        rewrite LemmaInt.Clt_Zlt_unsigned in H1, H2.
        replace (Int.unsigned (Int.repr 3)) with 3%Z in H1 by reflexivity.
        replace (Int.unsigned (Int.repr 11)) with 11%Z in H2 by reflexivity.
        rewrite int_unsigned_repr_int in *.
        unfold rbpf_arm_callee_save.
        destruct a; simpl in H1, H2; try lia; in_solver.
      }
      specialize (STK _ Heq) as HSTK_a; clear Heq.
      destruct HSTK_a as (HSTK_a & _).
      assert (Heq: In a (set_union breg_eq (a :: ld_set) [])). {
        apply set_union_intro1. left; auto.
      }
      specialize (HSTK_a Heq); clear Heq.
      rewrite HSTK_a.

    assert (Heq: is_final_state ars1 = false). {
      unfold is_final_state.
      assert (Heq: aval_eq (ars1 IR13) (Aval (Rval (Sreg IR13))) = false).
      - rewrite HIR13.
        simpl.
        auto.
      - rewrite Heq.
        rewrite andb_false_r.
        rewrite andb_false_l.
        auto.
    }
    rewrite Heq; clear Heq.

    assert (Heq: is_final_state (anextinstr true
         ars1 # (ireg_of_breg a) <-
         (Aval (Rval (Sreg (ireg_of_breg a))))) = false). {
      unfold is_final_state.
      assert (Heq: aval_eq ((anextinstr true
         ars1 # (ireg_of_breg a) <-
         (Aval (Rval (Sreg (ireg_of_breg a))))) IR13) (Aval (Rval (Sreg IR13))) = false).
      - unfold anextinstr.
        repeat abreg_solver_error_prone.
        rewrite HIR13.
        simpl.
        auto.
      - rewrite Heq.
        rewrite andb_false_r.
        rewrite andb_false_l.
        auto.
    }
    rewrite Heq; clear Heq.


      eexists. split; auto.
      split.
      2:{ 
        unfold anextinstr, aundef_flags; repeat abreg_solver.
        rewrite Pregmap.gso. auto. destruct a; simpl; intro HF; inversion HF.
      }
      constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; repeat abreg_solver.
      - intros.
        specialize (Hfloat _ H).
        repeat float_preg_of_solver.
        repeat (destruct H as [H | H];
            [subst x; auto|]); inversion H.
      - destruct HNoDup as (HNoDup1 & HNoDup2);
        split; auto.
        apply NoDup_cons_iff in HNoDup1; destruct HNoDup1 as (_ & HNoDup1); auto.

      - repeat abreg_solver_error_prone.
        assert (Hneq: IR0 <> ireg_of_breg a).
        + clear - Hcallee.
          intros HF.
          assert (Heq: a = R0).
          * clear - HF.
            unfold ireg_of_breg in HF.
            destruct a; inversion HF; auto.
          * subst a.
            unfold int_of_breg in Hcallee.
            simpl in Hcallee.
            change (Int.ltu (Int.repr 3) (Int.repr 0)) with false in Hcallee.
            rewrite andb_false_l in Hcallee.
            inversion Hcallee.
        + rewrite Pregmap.gso.
          2:{ intro HF. apply Hneq. injection HF as Heq. assumption. }
          repeat abreg_solver.

      - destruct HIRPC as (va_pc & HIRPC).
        unfold aoffset_ptr.
        repeat abreg_solver_error_prone.
        rewrite Pregmap.gso. 2:{ unfold ireg_of_breg; intro HF; inversion HF. }
        rewrite HIRPC.
        simpl.
        eexists; f_equal.

      - intros. inversion H.
      - unfold match_regs in *.
        intros.
        specialize (REG r).
        destruct REG as (REG1 & REG2 & REG3).
        split.
        { intro Hin.
          destruct (breg_eq r a) as [Hr_eq | Hr_neq].
          - subst r.
            exfalso.  clear - Hin HNoDup.
            destruct HNoDup as (HNoDup1 & HNoDup2).
            apply NoDup_cons_iff in HNoDup1; destruct HNoDup1 as (HF & HNoDup1).
            apply HF.
            apply set_union_elim in Hin.
            destruct Hin as [Hin | Hin]; [| inversion Hin].
            auto.
          - assert (Heq: In r (set_union breg_eq (a :: ld_set) [])). {
              apply set_union_elim in Hin.
              destruct Hin as [Hin | Hin]; [| inversion Hin].
              apply set_union_intro1. right; auto.
            }
            specialize (REG1 Heq); clear Heq.
            destruct REG1 as (vr & Hrs_eq & Hars_eq).
            exists vr.
            split; [auto | ].
            repeat abreg_solver.
        }
        split.
        { intro Hin.
          destruct (breg_eq r a) as [Hr_eq | Hr_neq].
          - subst r. repeat abreg_solver.
          - destruct Hin as (Hin & Hin1).
            assert (Heq: ~ In r (set_union breg_eq (a :: ld_set) []) /\
              In r rbpf_arm_callee_save). {
              split; auto.
              intro HF. apply Hin.
              apply set_union_elim in HF.
              destruct HF as [HF | HF]; [| inversion HF].
              destruct HF as [HF | HF].
              + exfalso; apply Hr_neq; auto.
              + apply set_union_intro1; auto.
            }
            specialize (REG2 Heq); clear Heq.
            repeat abreg_solver.
        }
        { auto. }
      - unfold match_stack.
        split; auto.
        intros.
        specialize (STK _ H).
        destruct STK as (STK1 & STK2).
        split.
        + intros.
          apply STK1.
          apply set_union_elim in H0.
          destruct H0 as [HF | HF]; [| inversion HF].
          apply set_union_intro1; right; auto.
        + destruct (breg_eq r a) as [Hr_eq | Hr_neq].
          { subst r.
            intros. repeat abreg_solver. }
          intros. destruct H0 as (Hin & Hin1).
          assert (Heq: ~ In r (set_union breg_eq (a :: ld_set) []) /\
            In r rbpf_arm_callee_save). {
            split; auto.
            intro HF. apply Hin.
            apply set_union_elim in HF.
            destruct HF as [HF | HF]; [| inversion HF].
            destruct HF as [HF | HF].
            + exfalso; apply Hr_neq; auto.
            + apply set_union_intro1; auto.
          }
          specialize (STK2 Heq); clear Heq.
          repeat abreg_solver.
    }
    destruct Heq as (ars2 & Hexe2 & Hst2 & Hir2).
    assert (Heq: (
    exists ars0 : aregset,
    exec_bin_list (jit_alu32_thumb_reset1 ld_set)
    ars2 astk1 astkb1 am1 = ANext ars0 astk1 astkb1 am1 /\
  match_states jit_blk st_blk [] [] (State rs m) (AState ars0 astk1 astkb1 am1) /\
  ars0 IR11 = Aval (Rval (Sreg IR11))) -> (exists ars0 : aregset,
  exec_bin_list
    (encode_arm32 (encode_arm32 (int_of_breg a) (Int.mul (int_of_breg a) (Int.repr 4)) 12 4)
       (encode_arm32 (int_of_ireg IR13) LDR_I_OP 0 4) 16 16 :: jit_alu32_thumb_reset1 ld_set)
    ars1 astk1 astkb1 am1 = ANext ars0 astk1 astkb1 am1 /\
  match_states jit_blk st_blk [] [] (State rs m) (AState ars0 astk1 astkb1 am1) /\
  ars0 IR11 = Aval (Rval (Sreg IR11)))). {
      intro HF.
      destruct HF as (ars3 & Hexe3 & Hst).
      exists ars3.
      split; auto.
      replace (encode_arm32
             (encode_arm32 (int_of_breg a) (Int.mul (int_of_breg a) (Int.repr 4)) 12 4)
             (encode_arm32 (int_of_ireg IR13) LDR_I_OP 0 4) 16 16
           :: jit_alu32_thumb_reset1 ld_set) with
      ([encode_arm32
             (encode_arm32 (int_of_breg a) (Int.mul (int_of_breg a) (Int.repr 4)) 12 4)
             (encode_arm32 (int_of_ireg IR13) LDR_I_OP 0 4) 16 16] ++ (jit_alu32_thumb_reset1 ld_set))
      by reflexivity.
      eapply exec_bin_list_concat; eauto.
    }
    apply Heq; clear Heq.

    eapply IHld_set; eauto.
Qed.