From compcert Require Import Memory Memtype Integers Values Ctypes AST.
From Coq Require Import ZArith Lia.

From bpf.comm Require Import MemRegion rBPFValues rBPFAST rBPFMemType Flag Regs BinrBPF.
From bpf.monadicmodel Require Import Opcode.

From bpf.dxcomm Require Import DxIntegers DxValues DxNat.

From bpf.jit.havm Require Import HAVMMonadOp.

Open Scope Z_scope.
Open Scope monad_scope.

Definition get_src32 (x: nat8) (ins: int64): M valu32_t := 
  if Int.eq Int.zero (Int.and (nat8_to_int x) int32_8) then
    do imm    <-- get_immediate ins;
      returnM (sint32_to_vint imm)
  else
    do src    <-- get_src ins;
      eval_reg src.

Definition get_opcode_ins (ins: int64): M nat8 :=
  returnM (get_opcode ins).

Definition get_opcode_alu32 (op: nat8): M opcode_alu32 :=
  returnM (byte_to_opcode_alu32 op).

Definition get_opcode_branch (op: nat8): M opcode_branch :=
  returnM (byte_to_opcode_branch op).

Definition get_opcode_mem_ld_reg (op: nat8): M opcode_mem_ld_reg :=
  returnM (byte_to_opcode_mem_ld_reg op).

Definition get_opcode_mem_st_imm (op: nat8): M opcode_mem_st_imm :=
  returnM (byte_to_opcode_mem_st_imm op).

Definition get_opcode_mem_st_reg (op: nat8): M opcode_mem_st_reg :=
  returnM (byte_to_opcode_mem_st_reg op).

Definition get_opcode_nat (op: nat8): M opcode :=
  returnM (byte_to_opcode op).

Definition get_add (x y: valu32_t): M valu32_t := returnM (Val.add x y).

Definition get_sub (x y: valu32_t): M valu32_t := returnM (Val.sub x y).

Definition get_addr_ofs (x: valu32_t) (ofs: sint32_t): M valu32_t := returnM (Val.add x (sint32_to_vint ofs)).

Definition get_start_addr (mr: memory_region): M valu32_t := returnM (start_addr mr).

Definition get_block_size (mr: memory_region): M valu32_t := returnM (block_size mr).

Definition get_block_perm (mr: memory_region): M permission := returnM (block_perm mr).

Definition check_mem_aux2 (mr: memory_region) (perm: permission) (addr: valu32_t) (chunk: memory_chunk): M valptr8_t :=
  do start  <-- get_start_addr mr;
  do size   <-- get_block_size mr;
  do mr_perm  <-- get_block_perm mr;
  do lo_ofs <-- get_sub addr start;
  do hi_ofs <-- get_add lo_ofs (memory_chunk_to_valu32 chunk);
    if andb (andb
              (compu_le hi_ofs size)
              (andb (compu_le lo_ofs (memory_chunk_to_valu32_upbound chunk))
                    (comp_eq val32_zero (val32_modu lo_ofs (memory_chunk_to_valu32 chunk)))))
            (perm_ge mr_perm perm) then
      returnM (Val.add (block_ptr mr) lo_ofs) (**r Vptr b lo_ofs *)
    else
      returnM valptr_null (**r = 0 *).

Fixpoint check_mem_aux (num: nat) (perm: permission) (chunk: memory_chunk) (addr: valu32_t) (mrs: MyMemRegionsType) {struct num}: M valptr8_t :=
  match num with
  | O => returnM valptr_null
  | S n =>
    do cur_mr    <-- get_mem_region n mrs;
    do check_ptr <-- check_mem_aux2 cur_mr perm addr chunk;
    do is_null   <-- cmp_ptr32_nullM check_ptr;
      if is_null then
        check_mem_aux n perm chunk addr mrs
      else
        returnM check_ptr
  end.

Definition check_mem (perm: permission) (chunk: memory_chunk) (addr: valu32_t): M valptr8_t :=
  do mem_reg_num <-- eval_mrs_num;
  do mrs         <-- eval_mrs_regions;
  do check_ptr   <-- check_mem_aux mem_reg_num perm chunk addr mrs;
  do is_null     <-- cmp_ptr32_nullM check_ptr;
    if is_null then
      returnM valptr_null
    else
      returnM check_ptr.

(*
Definition step_opcode_alu32 (op: nat8): M unit :=
  do opcode_alu32 <-- get_opcode_alu32 op;
  if opcode_alu32_eqb opcode_alu32 op_BPF_ALU32_ILLEGAL_INS then
    upd_flag BPF_ILLEGAL_INSTRUCTION
  else
      jit_call. *)

Definition step_opcode_branch (dst32: valu32_t) (src32: valu32_t) (ofs: int) (op: nat8) : M unit :=
  do opcode_jmp <-- get_opcode_branch op;
  match opcode_jmp with
  | op_BPF_JA       =>
    if Nat.eqb op nat8_0x05 then
      do _ <-- upd_pc ofs; returnM tt
    else
      do _ <-- upd_flag BPF_ILLEGAL_INSTRUCTION; returnM tt
  | op_BPF_JEQ     =>
    if comp_eq dst32 src32 then
      do _ <-- upd_pc ofs; returnM tt
    else
      returnM tt
  | op_BPF_JGT     =>
    if compu_gt dst32 src32 then
      do _ <-- upd_pc ofs; returnM tt
    else
      returnM tt
  | op_BPF_JGE     =>
    if compu_ge dst32 src32 then
      do _ <-- upd_pc ofs; returnM tt
    else
      returnM tt
  | op_BPF_JLT     =>
    if compu_lt dst32 src32 then
      do _ <-- upd_pc ofs; returnM tt
    else
      returnM tt
  | op_BPF_JLE     =>
    if compu_le dst32 src32 then
      do _ <-- upd_pc ofs; returnM tt
    else
      returnM tt
  | op_BPF_JSET     =>
    if compu_set dst32 src32 then
      do _ <-- upd_pc ofs; returnM tt
    else
      returnM tt
  | op_BPF_JNE     =>
    if comp_ne dst32 src32 then
      do _ <-- upd_pc ofs; returnM tt
    else
      returnM tt
  | op_BPF_JSGT     =>
    if comp_gt dst32 src32 then
      do _ <-- upd_pc ofs; returnM tt
    else
      returnM tt
  | op_BPF_JSGE     =>
    if comp_ge dst32 src32 then
      do _ <-- upd_pc ofs; returnM tt
    else
      returnM tt
  | op_BPF_JSLT     =>
    if comp_lt dst32 src32 then
      do _ <-- upd_pc ofs; returnM tt
    else
      returnM tt
  | op_BPF_JSLE     =>
    if comp_le dst32 src32 then
      do _ <-- upd_pc ofs; returnM tt
    else
      returnM tt

  | op_BPF_CALL =>
    if Nat.eqb op nat8_0x85 then
      do f_ptr    <-- _bpf_get_call (uvint_to_svint src32);
      do is_null  <-- cmp_ptr32_nullM f_ptr;
        if is_null then
          upd_flag BPF_ILLEGAL_CALL
        else
          do res  <-- exec_function f_ptr;
            upd_reg R0 res
    else
      do _ <-- upd_flag BPF_ILLEGAL_INSTRUCTION; returnM tt

  | op_BPF_RET => 
    if Nat.eqb op nat8_0x95 then
      do _ <-- upd_flag BPF_SUCC_RETURN; returnM tt
    else
      do _ <-- upd_flag BPF_ILLEGAL_INSTRUCTION; returnM tt
  | op_BPF_JMP_ILLEGAL_INS =>
      do _ <-- upd_flag BPF_ILLEGAL_INSTRUCTION; returnM tt
  end.

Definition step_opcode_mem_ld_reg (addr: valu32_t) (dst: reg) (op: nat8): M unit :=
  do opcode_ld <-- get_opcode_mem_ld_reg op;
  match opcode_ld with
  | op_BPF_LDXW      =>
    do addr_ptr <-- check_mem Readable Mint32 addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do v <-- load_mem Mint32 addr_ptr;
        do _ <-- upd_reg dst v; returnM tt
  | op_BPF_LDXH      =>
    do addr_ptr <-- check_mem Readable Mint16unsigned addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do v <-- load_mem Mint16unsigned addr_ptr;
        do _ <-- upd_reg dst v; returnM tt
  | op_BPF_LDXB      =>
    do addr_ptr <-- check_mem Readable Mint8unsigned addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do v <-- load_mem Mint8unsigned addr_ptr;
        do _ <-- upd_reg dst v; returnM tt
  | op_BPF_LDX_REG_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Definition step_opcode_mem_st_imm (imm: vals32_t) (addr: valu32_t) (op: nat8): M unit :=
  do opcode_st <-- get_opcode_mem_st_imm op;
  match opcode_st with
  | op_BPF_STW       =>
    do addr_ptr <-- check_mem Writable Mint32 addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <-- store_mem addr_ptr Mint32 (svint_to_uvint imm); returnM tt
  | op_BPF_STH       =>
    do addr_ptr <-- check_mem Writable Mint16unsigned addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <-- store_mem addr_ptr Mint16unsigned (svint_to_uvint imm); returnM tt
  | op_BPF_STB       =>
    do addr_ptr <-- check_mem Writable Mint8unsigned addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <-- store_mem addr_ptr Mint8unsigned (svint_to_uvint imm); returnM tt
  | op_BPF_ST_IMM_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Definition step_opcode_mem_st_reg (src32: valu32_t) (addr: valu32_t) (op: nat8): M unit :=
  do opcode_st <-- get_opcode_mem_st_reg op;
  match opcode_st with
  | op_BPF_STXW      =>
    do addr_ptr <-- check_mem Writable Mint32 addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <-- store_mem addr_ptr Mint32 src32; returnM tt
  | op_BPF_STXH      =>
    do addr_ptr <-- check_mem Writable Mint16unsigned addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <-- store_mem addr_ptr Mint16unsigned src32; returnM tt
  | op_BPF_STXB      =>
    do addr_ptr <-- check_mem Writable Mint8unsigned addr;
    do is_null  <-- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <-- store_mem addr_ptr Mint8unsigned src32; returnM tt
  | op_BPF_STX_REG_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Definition step: M unit :=
  do ins  <-- eval_ins;
  do op   <-- get_opcode_ins ins;
  do opc  <-- get_opcode_nat op;
  do dst  <-- get_dst ins;
  match opc with
  | op_BPF_ALU32   => jit_call
  | op_BPF_Branch  =>
    do dst32  <-- eval_reg dst;
    do ofs    <-- get_offset ins;
      (**r #define BPF_INSTRUCTION_ALU_S_MASK      0x08 *)
    do src32  <-- get_src32 op ins;
      step_opcode_branch dst32 src32 (sint32_to_uint32 ofs) op                    (**r 0xX5 / 0xXd *)
  | op_BPF_Mem_ld_reg  =>
    do src    <-- get_src ins;
    do src32  <-- eval_reg src;
    do ofs    <-- get_offset ins;
    do addr   <-- get_addr_ofs src32 ofs;
      step_opcode_mem_ld_reg addr dst op       (**r 0xX1/0xX9 *)
  | op_BPF_Mem_st_imm  =>
    do dst32  <-- eval_reg dst;
    do ofs    <-- get_offset ins;
    do imm    <-- get_immediate ins;
    do addr   <-- get_addr_ofs dst32 ofs;
      step_opcode_mem_st_imm (sint32_to_vint imm) addr op       (**r 0xX2/0xXa *)
  | op_BPF_Mem_st_reg  =>
    do dst32  <-- eval_reg dst;
    do src    <-- get_src ins;
    do src32  <-- eval_reg src;
    do ofs    <-- get_offset ins;
    do addr   <-- get_addr_ofs dst32 ofs;
      step_opcode_mem_st_reg src32 addr op       (**r 0xX3/0xXb *)
  | op_BPF_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Fixpoint bpf_interpreter_aux (fuel: nat) {struct fuel}: M unit :=
  match fuel with
  | O => upd_flag BPF_ILLEGAL_LEN
  | S fuel0 =>
    do b0   <-- check_pc;
      if b0 then
        do _ <-- step;
        do f <-- eval_flag;
          if flag_eq f BPF_OK then
            do b1  <-- check_pc_incr;
              if b1 then
                do _ <-- upd_pc Int.one;
                  bpf_interpreter_aux fuel0
              else
                upd_flag BPF_ILLEGAL_LEN
          else
            returnM tt
      else
        upd_flag BPF_ILLEGAL_LEN
  end.

Definition havm_interpreter (fuel: nat) (ctx_ptr: valu32_t): M valu32_t :=
  do _        <-- upd_reg R1 ctx_ptr;
  do _        <-- bpf_interpreter_aux fuel;
  do f        <-- eval_flag;
    if flag_eq f BPF_SUCC_RETURN then
      do res  <-- eval_reg R0;
        returnM res
    else
      returnM val32_zero.

Close Scope monad_scope.
Close Scope Z_scope.