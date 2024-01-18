From compcert Require Import Integers.
From compcert.arm Require Import AsmSyntax BinSyntax BinDecode.

From bpf.comm Require Import Flag BinrBPF ListAsArray Regs rBPFValues.
From bpf.dxcomm Require Import DxIntegers DxNat.
From bpf.rbpf32 Require Import JITConfig.
From bpf.jit Require Import ThumbInsOp ListSetRefinement.
From bpf.jit.jitcompiler Require Import JITMonadOp ThumbJITOpcode JITNat DxMonadCommon.

From Coq Require Import List ZArith Arith String.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope asm.
Open Scope string_scope.
Open Scope monad_scope.

Definition decode_thumb (ins: int) (from size: nat): M int :=
  returnM (decode_arm32 ins from size).

Definition encode_thumb (v ins: int16) (from size: nat): M int :=
  returnM (encode_arm32 v ins from size).

(*
Definition opcode_reg_of_imm (op: opcode_alu32_imm): M opcode_alu32_reg :=
  returnM (opcode_reg_of_imm op). *)

Definition ins_is_bpf_alu32 (ins: int64) : M bool := returnM (ins_is_bpf_alu32 ins).

Definition ins_is_bpf_jump (ins: int64) : M bool := returnM (ins_is_bpf_jump ins).

Definition jit_alu32_thumb_mem_template_jit (op rt rn imm12: int16): M int :=
  do str_low   <-- encode_thumb rn op 0 nat_4;
  do str_high  <-- encode_thumb rt imm12 nat_12 nat_4;
    encode_thumb str_high str_low nat_16 nat_16.

(** * Pre Stage *)
Definition jit_alu32_pre: M unit :=
  do ins_rdn <-- encode_thumb int16_4 MOV_R_OP 0 nat_3;
  do ins_rm  <-- encode_thumb int16_1 ins_rdn nat_3 nat_4;
  do ins     <-- encode_thumb int16_1 ins_rm nat_7 nat_1;
  do ins32   <-- encode_thumb ins NOP_OP nat_16 nat_16;
    add_jited_bin ins32. (*;
  do str     <-- jit_alu32_thumb_mem_template_jit STR_I_OP int16_11 int16_13 int16_44;
    add_jited_bin str. *)

Definition jit_call_save_add (r: reg): M unit :=
  do cond <-- eval_load_regset r;
    if cond then returnM tt
    else
      do ldr_ins <-- jit_alu32_thumb_mem_template_jit LDR_I_OP (int16_of_reg r) int16_12
                    (int16_mul (int16_of_reg r) int16_4);
        if andb (int16_ltu int16_3 (int16_of_reg r)) (int16_ltu (int16_of_reg r) int16_12) then
          do str_ins <-- jit_alu32_thumb_mem_template_jit STR_I_OP (int16_of_reg r) int16_13
                        (int16_mul (int16_of_reg r) int16_4);
          do _       <-- add_jited_bin str_ins;
            add_jited_bin ldr_ins
          else
            add_jited_bin ldr_ins.

Definition jit_call_save_reg (dst src: reg): M unit :=
  do _ <-- jit_call_save_add dst;
  do _ <-- upd_load_regset dst;
  do _ <-- upd_store_regset dst;

  do _ <-- jit_call_save_add src;
    upd_load_regset src.

Definition jit_call_save_imm (dst: reg): M unit :=
  do _ <-- jit_call_save_add dst;
  do _ <-- upd_load_regset dst;
    upd_store_regset dst.

Definition bpf_alu32_to_thumb_reg_comm (op: int16) (dst src: int16): M unit :=
  do ins_lo  <-- encode_thumb dst op 0 nat_4;
  do ins_hi  <-- encode_thumb dst src nat_8 nat_4;
  do ins32   <-- encode_thumb ins_hi ins_lo nat_16 nat_16;
    add_jited_bin ins32.

Definition bpf_alu32_to_thumb_reg (op: opcode_alu32_reg) (dst src: int16): M unit :=
  match op with
  | BPF_ADD32_REG =>
    do d       <-- if int16_lt dst int16_8 then returnM int16_0 else returnM int16_1;
    do rdn     <-- if int16_lt dst int16_8 then
                      returnM dst
                    else
                      returnM (int16_sub dst int16_8);
    do ins_rdn <-- encode_thumb rdn ADD_R_OP 0 nat_3;
    do ins_rm  <-- encode_thumb src ins_rdn nat_3 nat_4;
    do ins     <-- encode_thumb d ins_rm nat_7 nat_1;
    do ins32   <-- encode_thumb ins NOP_OP nat_16 nat_16;
      add_jited_bin ins32

  | BPF_SUB32_REG => bpf_alu32_to_thumb_reg_comm SUB_R_OP dst src

  | BPF_MUL32_REG =>
    do ins_lo  <-- encode_thumb dst MUL_OP 0 nat_4;
    do ins_hi0 <-- encode_thumb dst src nat_8 nat_4;
    do ins_hi  <-- encode_thumb int16_15 ins_hi0 nat_12 nat_4;
    do ins32   <-- encode_thumb ins_hi ins_lo nat_16 nat_16;
      add_jited_bin ins32
(*
  | BPF_DIV32_REG => returnM tt *)
  | BPF_OR32_REG => bpf_alu32_to_thumb_reg_comm ORR_R_OP dst src
  | BPF_AND32_REG => bpf_alu32_to_thumb_reg_comm AND_R_OP dst src

  | BPF_LSH32_REG =>
    do ins_lo  <-- encode_thumb dst LSL_R_OP 0 nat_4;
    do ins_hi0 <-- encode_thumb dst src nat_8 nat_4;
    do ins_hi  <-- encode_thumb int16_15 ins_hi0 nat_12 nat_4;
    do ins32   <-- encode_thumb ins_hi ins_lo nat_16 nat_16;
      add_jited_bin ins32
  | BPF_RSH32_REG =>
    do ins_lo  <-- encode_thumb dst LSR_R_OP 0 nat_4;
    do ins_hi0 <-- encode_thumb dst src nat_8 nat_4;
    do ins_hi  <-- encode_thumb int16_15 ins_hi0 nat_12 nat_4;
    do ins32   <-- encode_thumb ins_hi ins_lo nat_16 nat_16;
      add_jited_bin ins32

  | BPF_XOR32_REG => bpf_alu32_to_thumb_reg_comm EOR_R_OP dst src
  | BPF_MOV32_REG =>
    if int16_eq dst src then
      returnM tt
    else
      do d       <-- if Int.lt dst int16_8 then returnM int16_0 else returnM int16_1;
      do rdn     <-- if Int.lt dst int16_8 then
                        returnM dst
                      else
                        returnM (int16_sub dst int16_8);
      do ins_rdn <-- encode_thumb rdn MOV_R_OP 0 nat_3;
      do ins_rm  <-- encode_thumb src  ins_rdn nat_3 nat_4;
      do ins     <-- encode_thumb d ins_rm nat_7 nat_1;
      do ins32   <-- encode_thumb ins NOP_OP nat_16 nat_16;
        add_jited_bin ins32
  | BPF_ARSH32_REG =>
    do ins_lo  <-- encode_thumb dst ASR_R_OP 0 nat_4;
    do ins_hi0 <-- encode_thumb dst src nat_8 nat_4;
    do ins_hi  <-- encode_thumb int16_15 ins_hi0 nat_12 nat_4;
    do ins32   <-- encode_thumb ins_hi ins_lo nat_16 nat_16;
      add_jited_bin ins32

  | BPF_ALU32_REG_ILLEGAL_INS => returnM tt
  end.

Definition load_IR11: M unit :=
  do f <-- eval_use_IR11;
    if f then
      returnM tt
    else
      do _    <-- upd_IR11_jittedthumb true;
      do str  <-- jit_alu32_thumb_mem_template_jit STR_I_OP int16_11 int16_13 int16_44;
        add_jited_bin str.


Definition mov_int_to_movwt (i: int) (r op: int16): M unit :=
  do _         <-- load_IR11;
  do lo_imm8   <-- decode_thumb i 0       nat_8;
  do lo_imm3   <-- decode_thumb i nat_8   nat_3;
  do lo_i      <-- decode_thumb i nat_11  nat_1;
  do lo_imm4   <-- decode_thumb i nat_12  nat_4;

  do movw_lo_0 <-- encode_thumb lo_imm4 op        0       nat_4;
  do movw_lo   <-- encode_thumb lo_i    movw_lo_0 nat_10  nat_1;

  do movw_hi_0 <-- encode_thumb r       lo_imm8   nat_8   nat_4;
  do movw_hi   <-- encode_thumb lo_imm3 movw_hi_0 nat_12  nat_3;
  do ins32     <-- encode_thumb movw_hi movw_lo nat_16 nat_16;
    add_jited_bin ins32.

Definition bpf_alu32_to_thumb_imm_comm (op: int16) (alu_op: opcode_alu32_reg) (dst: int16) (imm32: int): M unit :=
  if (Int_leu Int.zero imm32) && (Int_leu imm32 int32_0xff) then (**r 0 <= imm32 <= 255 *)
    do ins_lo    <-- encode_thumb dst op 0 nat_4;
    do ins_hi    <-- encode_thumb dst imm32 nat_8 nat_4;
    do ins32     <-- encode_thumb ins_hi ins_lo nat_16 nat_16;
      add_jited_bin ins32
  else
    do lo_32 <-- decode_thumb imm32 0 nat_16;
    do hi_32 <-- decode_thumb imm32 nat_16 nat_16;
    do _ <-- mov_int_to_movwt lo_32 int16_11 MOVW_OP;
      if Int.eq lo_32 imm32 then (**r optimization: if high_16 = 0 then only add `movw` *)
        bpf_alu32_to_thumb_reg alu_op dst int16_11
      else (**r optimization: if high_16 <> 0 then add`movt + movw` *)
        do _ <-- mov_int_to_movwt hi_32 int16_11 MOVT_OP;
          bpf_alu32_to_thumb_reg alu_op dst int16_11.

Definition bpf_alu32_to_thumb_imm_shift_comm (op: int16) (dst: int16) (imm32: int): M unit :=
  if (Int_leu Int.zero imm32) && (Int.ltu imm32 int32_32) then
    do ins_lo  <-- encode_thumb dst op 0 nat_4;
    do ins_hi0 <-- encode_thumb dst int16_11 nat_8 nat_4;
    do ins_hi  <-- encode_thumb int16_15 ins_hi0 nat_12 nat_4;
    do ins32   <-- encode_thumb ins_hi ins_lo nat_16 nat_16;
    do _       <-- mov_int_to_movwt imm32 int16_11 MOVW_OP;
      add_jited_bin ins32
  else
    returnM tt.

Definition bpf_alu32_to_thumb_imm (op: opcode_alu32_imm) (dst: int16) (imm32: int): M unit :=
  match op with
  | BPF_ADD32_IMM => bpf_alu32_to_thumb_imm_comm ADD_I_OP BPF_ADD32_REG dst imm32
  | BPF_SUB32_IMM => bpf_alu32_to_thumb_imm_comm SUB_I_OP BPF_SUB32_REG dst imm32
  | BPF_MUL32_IMM =>
    do lo_32 <-- decode_thumb imm32 0 nat_16;
    do hi_32 <-- decode_thumb imm32 nat_16 nat_16;
    do _     <-- mov_int_to_movwt lo_32 int16_11 MOVW_OP;
      if Int.eq lo_32 imm32 then (**r optimization: if high_16 = 0 then only add `movw` *)
        bpf_alu32_to_thumb_reg BPF_MUL32_REG dst int16_11
      else 
        do _ <-- mov_int_to_movwt hi_32 int16_11 MOVT_OP;
          bpf_alu32_to_thumb_reg BPF_MUL32_REG dst int16_11
  | BPF_DIV32_IMM   => (**r CompCert doesn't have div_imm, so we do `mov + div_reg` *)
    if Int.eq imm32 Int.zero then
      returnM tt
    else 
      (**r construct: udiv Rd Rn Rm *)
      do ins_lo  <-- encode_thumb dst UDIV_LO_OP 0 nat_4;
      do ins_hi0 <-- encode_thumb dst UDIV_HI_OP nat_8 nat_4;
      do ins_hi  <-- encode_thumb int16_11 ins_hi0 0 nat_4;
      do ins32   <-- encode_thumb ins_hi ins_lo nat_16 nat_16;

      do lo_32   <-- decode_thumb imm32 0 nat_16;
      do hi_32   <-- decode_thumb imm32 nat_16 nat_16;
      do _       <-- mov_int_to_movwt lo_32 int16_11 MOVW_OP;
        if Int.eq lo_32 imm32 then (**r optimization: if high_16 = 0 then only add `movw` *)
          add_jited_bin ins32
        else (**r optimization: if high_16 <> 0 then add`movt + movw` *)
          do _   <-- mov_int_to_movwt hi_32 int16_11 MOVT_OP;
            add_jited_bin ins32
  | BPF_OR32_IMM  => bpf_alu32_to_thumb_imm_comm ORR_I_OP BPF_OR32_REG dst imm32
  | BPF_AND32_IMM => bpf_alu32_to_thumb_imm_comm AND_I_OP BPF_AND32_REG dst imm32

  | BPF_LSH32_IMM   => bpf_alu32_to_thumb_imm_shift_comm LSL_R_OP dst imm32
  | BPF_RSH32_IMM   => bpf_alu32_to_thumb_imm_shift_comm LSR_R_OP dst imm32

  | BPF_NEG32_IMM =>
    do ins_lo    <-- encode_thumb int16_11 RSB_I_OP 0 nat_4;
    do ins_hi    <-- encode_thumb dst int16_0 nat_8 nat_4;
    do ins32     <-- encode_thumb ins_hi ins_lo nat_16 nat_16;
    do lo_32     <-- decode_thumb imm32 0 nat_16;
    do hi_32     <-- decode_thumb imm32 nat_16 nat_16;
    do _         <-- mov_int_to_movwt lo_32 int16_11 MOVW_OP;
      if Int.eq lo_32 imm32 then (**r optimization: if high_16 = 0 then only add `movw` *)
        add_jited_bin ins32
      else (**r optimization: if high_16 <> 0 then add`movt + movw` *)
        do _   <-- mov_int_to_movwt hi_32 int16_11 MOVT_OP;
          add_jited_bin ins32

  | BPF_XOR32_IMM => bpf_alu32_to_thumb_imm_comm EOR_I_OP BPF_XOR32_REG dst imm32
  | BPF_MOV32_IMM =>
    do lo_32 <-- decode_thumb imm32 0 nat_16;
    do hi_32 <-- decode_thumb imm32 nat_16 nat_16;
    do _     <-- mov_int_to_movwt lo_32 dst MOVW_OP;
      if Int.eq lo_32 imm32 then (**r optimization: if high_16 = 0 then only add `movw` *)
        returnM tt
      else (**r optimization: if high_16 <> 0 then add`movt + movw` *)
        mov_int_to_movwt hi_32 dst MOVT_OP
  | BPF_ARSH32_IMM  => bpf_alu32_to_thumb_imm_shift_comm ASR_R_OP dst imm32
  | _ => returnM tt
  end.

Definition nat_to_opcode_alu32 (op: nat8): M opcode_alu32 :=
  if Int.eq (Int.and (nat8_to_int op) int32_7) int32_4 then
    if Int.eq Int.zero (Int.and (nat8_to_int op) int32_8) then
      returnM ALU32_IMM
    else
      returnM ALU32_REG
  else
    returnM ALU32_ILLEGAL_INS.

Definition nat_to_opcode_alu32_reg (op: nat8): M opcode_alu32_reg := returnM (nat_to_opcode_alu32_reg op).

Definition nat_to_opcode_alu32_imm (op: nat8): M opcode_alu32_imm := returnM (nat_to_opcode_alu32_imm op).

Definition jit_one (ins: int64): M bool :=
  do op    <-- get_opcode_ins ins;
  do opc   <-- nat_to_opcode_alu32 op;
  do dst   <-- get_dst ins;
  do imm32 <-- get_immediate ins;
    match opc with
    | ALU32_REG =>
      do opr  <-- nat_to_opcode_alu32_reg op;
      do src  <-- get_src ins;
      do _    <-- jit_call_save_reg dst src;
      do _    <-- bpf_alu32_to_thumb_reg opr (int16_of_reg dst) (int16_of_reg src);
        returnM true

    | ALU32_IMM =>
      do opi <-- nat_to_opcode_alu32_imm op;
      do _   <-- jit_call_save_imm dst;
      do _    <-- bpf_alu32_to_thumb_imm opi (int16_of_reg dst) imm32;
        returnM true
    | ALU32_ILLEGAL_INS => returnM false
    end.

Fixpoint jit_sequence (fuel pc counter: nat): M nat :=
  match fuel with
  | O => returnM counter
  | S n =>
    do ins64 <-- eval_input_ins pc;
    do cond  <-- jit_one ins64;
      if cond then
        jit_sequence n (Nat.add pc nat_1) (Nat.add counter nat_1)
      else
        returnM counter
  end.

(*
Definition jit_alu32_thumb_pc_add (imm32: int): M unit :=
  if (Int_leu Int.zero imm32) && (Int.ltu imm32 int32_0xff) then (**r 0 <= imm32 <= 255 *)
    do ins_lo    <-- encode_thumb int16_11 ADD_I_OP 0 nat_4;
    do ins_hi    <-- encode_thumb int16_11 imm32 nat_8 nat_4;
    do ins32     <-- encode_thumb ins_hi ins_lo nat_16 nat_16;
      add_jited_bin ins32
  else
    returnM tt.

Definition jit_alu32_thumb_pc (num: nat): M unit :=
  do l_ldr  <-- jit_alu32_thumb_mem_template_jit LDR_I_OP int16_11 int16_12 int16_44;
  do _      <-- add_jited_bin l_ldr;
  do _      <-- jit_alu32_thumb_pc_add (nat_to_int32 num);
  do l_str  <-- jit_alu32_thumb_mem_template_jit STR_I_OP int16_11 int16_12 int16_44;
    add_jited_bin l_ldr. *)

Definition jit_alu32_thumb_upd_store (r: reg): M unit :=
  do cond <-- eval_store_regset r;
    if cond then
      do ins32 <-- jit_alu32_thumb_mem_template_jit STR_I_OP (int16_of_reg r) int16_12
                      (int16_mul (int16_of_reg r) int16_4);
        add_jited_bin ins32
    else
      returnM tt.

Definition jit_alu32_thumb_store: M unit :=
  do _ <-- jit_alu32_thumb_upd_store R0;
  do _ <-- jit_alu32_thumb_upd_store R1;
  do _ <-- jit_alu32_thumb_upd_store R2;
  do _ <-- jit_alu32_thumb_upd_store R3;
  do _ <-- jit_alu32_thumb_upd_store R4;
  do _ <-- jit_alu32_thumb_upd_store R5;
  do _ <-- jit_alu32_thumb_upd_store R6;
  do _ <-- jit_alu32_thumb_upd_store R7;
  do _ <-- jit_alu32_thumb_upd_store R8;
  do _ <-- jit_alu32_thumb_upd_store R9;
    jit_alu32_thumb_upd_store R10.


Definition jit_alu32_thumb_upd_reset (r: reg): M unit :=
  do cond <-- eval_load_regset r;
    if cond then
      do ins32 <-- jit_alu32_thumb_mem_template_jit LDR_I_OP (int16_of_reg r) int16_13
                      (int16_mul (int16_of_reg r) int16_4);
        add_jited_bin ins32
    else
      returnM tt.

Definition jit_alu32_thumb_reset1: M unit :=
  do _ <-- jit_alu32_thumb_upd_reset R4;
  do _ <-- jit_alu32_thumb_upd_reset R5;
  do _ <-- jit_alu32_thumb_upd_reset R6;
  do _ <-- jit_alu32_thumb_upd_reset R7;
  do _ <-- jit_alu32_thumb_upd_reset R8;
  do _ <-- jit_alu32_thumb_upd_reset R9;
    jit_alu32_thumb_upd_reset R10.

Definition jit_alu32_thumb_reset: M unit :=
  do f <-- eval_use_IR11;
  do _ <--
    if f then
      do l_ldr  <-- jit_alu32_thumb_mem_template_jit LDR_I_OP int16_11 int16_13 int16_44;
        add_jited_bin l_ldr
    else returnM tt;
    jit_alu32_thumb_reset1.

Definition jit_alu32_post: M unit :=
  do l_ldr  <-- jit_alu32_thumb_mem_template_jit LDR_I_OP int16_13 int16_13 int16_0;
  do ins_rm <-- encode_thumb int16_14 BX_OP nat_3 nat_4;
  do ins32  <-- encode_thumb ins_rm NOP_OP nat_16 nat_16;
  do _      <-- add_jited_bin l_ldr;
    add_jited_bin ins32.

Definition jit_alu32_aux (fuel pc counter: nat): M nat :=
  do _ <-- jit_alu32_pre;
  do n <-- jit_sequence fuel pc counter; (*
  do _ <-- jit_alu32_thumb_pc n; *)
  do _ <-- jit_alu32_thumb_store;
  do _ <-- jit_alu32_thumb_reset;
  do _ <-- jit_alu32_post;
    returnM n.

Definition jit_list (fuel pc: nat): M nat :=
  do _ <-- reset_init_jittedthumb;
    jit_alu32_aux fuel pc 0.

Fixpoint whole_compiler_aux (fuel pc: nat): M unit :=
  match fuel with
  | O => returnM tt
  | S n =>
    do len <-- eval_input_len;
      if Nat.eqb len pc then
        returnM tt
      else
        do ins64 <-- eval_input_ins pc;
        do b     <-- ins_is_bpf_alu32 ins64;
          if b then
            do arm_ofs  <-- eval_arm_ofs;
            do sz       <-- jit_list (Nat.sub len pc) pc;
            do _        <-- add_key_value pc arm_ofs sz;
              whole_compiler_aux n (Nat.add pc sz)
          else
            do b <-- ins_is_bpf_jump ins64;
            if b then
              do ofs      <-- get_offset ins64;
              do next_pc  <-- returnM (int32_to_nat (Int.add (Int.add (int_of_nat pc) ofs) Int.one));
              do next_ins <-- eval_input_ins next_pc;
              do b        <-- ins_is_bpf_alu32 next_ins;
                if b then
                  do arm_ofs  <-- eval_arm_ofs;
                  do sz       <-- jit_list (Nat.sub len next_pc) next_pc;
                  do _        <-- add_key_value next_pc arm_ofs sz;
                    whole_compiler_aux n (Nat.add pc nat_1)
                else
                  whole_compiler_aux n (Nat.add pc nat_1)
          else (**r when ins is not jump *)
            whole_compiler_aux n (Nat.add pc nat_1)
  end.


Definition whole_compiler: M unit :=
  do len  <-- eval_input_len;
    whole_compiler_aux len 0.

Close Scope monad_scope.
Close Scope string_scope.
Close Scope asm.
Close Scope bool_scope.
Close Scope Z_scope.