(**************************************************************************)
(*  This file is part of CertrBPF,                                        *)
(*  a formally verified rBPF verifier + interpreter + JIT in Coq.         *)
(*                                                                        *)
(*  Copyright (C) 2022 Inria                                              *)
(*                                                                        *)
(*  This program is free software; you can redistribute it and/or modify  *)
(*  it under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation; either version 2 of the License, or     *)
(*  (at your option) any later version.                                   *)
(*                                                                        *)
(*  This program is distributed in the hope that it will be useful,       *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU General Public License for more details.                          *)
(*                                                                        *)
(**************************************************************************)

From compcert Require Import Memory Memtype Integers Values Ctypes AST.
From Coq Require Import ZArith Lia.

From bpf.comm Require Import Flag rBPFValues Regs BinrBPF State Monad MemRegion rBPFAST rBPFMemType rBPFMonadOp.
From bpf.model Require Import Syntax Decode.

Open Scope monad_scope.

Definition eval_src (s:reg+imm): M state val :=
  match s with
  | inl r => eval_reg r
  | inr i => returnM (sint32_to_vint i) (**r the immediate is always int *)
  end.

Definition step_branch_cond (c: cond) (d: reg) (s: reg+imm): M state bool :=
  do dst <- eval_reg d;
  do src <- eval_src s;
  returnM (match c with
  | Eq  => comp_eq   dst src
  | SEt => compu_set dst src
  | Ne  => comp_ne   dst src
  | Gt sign => 
    match sign with
    | Unsigned => compu_gt dst src
    | Signed   => comp_gt  dst src
    end
  | Ge sign =>
    match sign with
    | Unsigned => compu_ge dst src
    | Signed   => comp_ge  dst src
    end
  | Lt sign => 
    match sign with
    | Unsigned => compu_lt dst src
    | Signed   => comp_lt  dst src
    end
  | Le sign => 
    match sign with
    | Unsigned => compu_le dst src
    | Signed   => comp_le  dst src
    end
  end).

Definition get_add (x y: val): M state val := returnM (Val.add x y).

Definition get_sub (x y: val): M state val := returnM (Val.sub x y).

Definition get_addr_ofs (x: val) (ofs: int): M state val := returnM ((Val.add x (sint32_to_vint ofs))).

Definition get_start_addr (mr: memory_region): M state val := returnM (start_addr mr).

Definition get_block_size (mr: memory_region): M state val := returnM (block_size mr).

Definition get_block_perm (mr: memory_region): M state permission := returnM (block_perm mr).

Definition check_mem_aux2 (mr: memory_region) (perm: permission) (addr: val) (chunk: memory_chunk): M state val :=
  do start  <- get_start_addr mr;
  do size   <- get_block_size mr;
  do mr_perm  <- get_block_perm mr;
  do lo_ofs <- get_sub addr start;
  do hi_ofs <- get_add lo_ofs (memory_chunk_to_valu32 chunk);
    if andb (andb
              (compu_le hi_ofs size)
              (andb (compu_le lo_ofs (memory_chunk_to_valu32_upbound chunk))
                    (comp_eq Vzero (val32_modu lo_ofs (memory_chunk_to_valu32 chunk)))))
            (perm_ge mr_perm perm) then
            returnM (Val.add (block_ptr mr) lo_ofs) (**r Vptr b lo_ofs *)
    else
      returnM Vnullptr.

Fixpoint check_mem_aux (num: nat) (perm: permission) (chunk: memory_chunk) (addr: val) (mrs: MyMemRegionsType) {struct num}: M state val :=
  match num with
  | O => returnM Vnullptr
  | S n =>
    do cur_mr     <- get_mem_region n mrs;
    do check_ptr  <- check_mem_aux2 cur_mr perm addr chunk;
    do is_null    <- cmp_ptr32_nullM check_ptr;
      if is_null then
        check_mem_aux n perm chunk addr mrs
      else
        returnM check_ptr
  end.

Definition check_mem (perm: permission) (chunk: memory_chunk) (addr: val): M state val :=
      do mem_reg_num  <- eval_mrs_num;
      do mrs          <- eval_mrs_regions;
      do check_ptr    <- check_mem_aux mem_reg_num perm chunk addr mrs;
      do is_null      <- cmp_ptr32_nullM check_ptr;
        if is_null then
          returnM Vnullptr
        else
          returnM check_ptr.

Definition step_load_x_operation (chunk: memory_chunk) (d:reg) (s:reg) (ofs:off): M state unit :=
  do m    <- eval_mem;
  do mrs  <- eval_mem_regions;
  do sv   <- eval_reg s;
  do addr <- get_addr_ofs sv ofs;
  do ptr  <- check_mem Readable chunk addr;
  do is_null   <- cmp_ptr32_nullM ptr;
    if is_null then
      upd_flag BPF_ILLEGAL_MEM
    else
      do v <- load_mem chunk ptr;
      do _ <- upd_reg d v; returnM tt
.

Definition step_store_operation (chunk: memory_chunk) (d: reg) (s: reg+imm) (ofs: off): M state unit :=
  do m    <- eval_mem;
  do mrs  <- eval_mem_regions;
  do dv   <- eval_reg d;
  do addr <- get_addr_ofs dv ofs;

    match s with
    | inl r =>
      do src <- eval_reg r;
      do ptr  <- check_mem Writable chunk addr;
      do is_null   <- cmp_ptr32_nullM ptr;
        if is_null then
          upd_flag BPF_ILLEGAL_MEM
        else
          do _ <- store_mem ptr chunk src; returnM tt
    | inr i =>
      do ptr  <- check_mem Writable chunk addr;
      do is_null   <- cmp_ptr32_nullM ptr;
        if is_null then
          upd_flag BPF_ILLEGAL_MEM
        else
          do _ <- store_mem ptr chunk (sint32_to_vint i); returnM tt
    end.

Definition decodeM (i: int64) : M state bpf_instruction := fun st =>
  match (decode i) with
  | Some ins => Some (ins, st)
  | None => None
  end.

Definition get_immediate (ins:int64): M state int := returnM (get_immediate ins).

Definition step : M state unit :=
  do ins64<- eval_ins;
  do ins  <- decodeM ins64;
    match ins with
    | BPF_NEG d => jit_call

    | BPF_BINARY bop d s => jit_call

    | BPF_JA ofs => upd_pc ofs
    | BPF_JUMP c d s ofs =>
      do cond <- step_branch_cond c d s;
      if cond then
        upd_pc ofs
      else
        returnM tt

    | BPF_LDX chunk d s ofs =>
      step_load_x_operation chunk d s ofs
    | BPF_ST chunk d s ofs =>
      step_store_operation chunk d s ofs

    | BPF_CALL i =>
      do f_ptr    <- _bpf_get_call (Vint ((Int.repr (Int.signed i))));
      do is_null  <- cmp_ptr32_nullM f_ptr;
        if is_null then
          upd_flag BPF_ILLEGAL_CALL
        else
          do res  <- exec_function f_ptr;
            upd_reg R0 res
    | BPF_RET    => upd_flag BPF_SUCC_RETURN
    | BPF_ERR    => upd_flag BPF_ILLEGAL_INSTRUCTION
    end.

Fixpoint bpf_interpreter_aux (fuel: nat) {struct fuel}: M state unit :=
  match fuel with
  | O => upd_flag BPF_ILLEGAL_LEN
  | S fuel0 =>
    do b0  <- check_pc;
      if b0 then
        do _    <- step;
        do f    <- eval_flag;
          if flag_eq f BPF_OK then
            do b1  <- check_pc_incr;
              if b1 then
                do _ <- upd_pc Int.one;
                  bpf_interpreter_aux fuel0
              else
                upd_flag BPF_ILLEGAL_LEN
          else
            returnM tt
      else
        upd_flag BPF_ILLEGAL_LEN
  end.

Definition bpf_interpreter (fuel: nat) (ctx_ptr: val): M state val :=
  do _        <- upd_reg R1 ctx_ptr;
  do _        <- bpf_interpreter_aux fuel;
  do f        <- eval_flag;
    if flag_eq f BPF_SUCC_RETURN then
      do res  <- eval_reg R0;
        returnM res
    else
      returnM Vzero.

Close Scope monad_scope.