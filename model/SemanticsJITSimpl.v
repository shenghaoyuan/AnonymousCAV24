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
From compcert.arm Require Import AsmSyntax ABinSem.
From Coq Require Import ZArith Lia List.

From bpf.comm Require Import Flag rBPFValues Regs BinrBPF MemRegion.
From bpf.comm Require Import rBPFAST rBPFMemType ListAsArray JITCall.
From bpf.model Require Import Syntax Decode.

Open Scope Z_scope.
Import ListNotations.

Definition eval_src (s:reg+imm) (rs: regmap): val :=
  match s with
  | inl r => eval_regmap r rs
  | inr i => sint32_to_vint i
  end.

Definition step_branch_cond (c: cond) (d: reg) (s: reg+imm) (rs: regmap): bool :=
  let dst := eval_regmap d rs in
  let src := eval_src s rs in
    match c with
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
    end.

Definition check_mem_aux2 (mr: memory_region) (perm: permission) (addr: val) (chunk: memory_chunk): val :=
  let lo_ofs := Val.sub addr (start_addr mr) in
  let hi_ofs := Val.add lo_ofs (memory_chunk_to_valu32 chunk) in
    if andb (andb
              (compu_le hi_ofs (block_size mr))
              (andb (compu_le lo_ofs (memory_chunk_to_valu32_upbound chunk))
                    (comp_eq Vzero (val32_modu lo_ofs (memory_chunk_to_valu32 chunk)))))
            (perm_ge (block_perm mr) perm) then
      Val.add (block_ptr mr) lo_ofs
    else
      Vnullptr.

Definition get_mem_region (n mrs_num: nat) (mrs: MyMemRegionsType): option memory_region :=
  if (Nat.ltb n mrs_num) then
    match List.nth_error mrs n with
    | Some mr => Some mr
    | None => None
    end
  else
    None.

(**r could be may abstract *)
Fixpoint check_mem_aux (num mrs_num: nat) (perm: permission) (chunk: memory_chunk) (addr: val) (mrs: MyMemRegionsType) (m: mem) {struct num}: option val :=
  match num with
  | O => Some Vnullptr
  | S n =>
    match get_mem_region n mrs_num mrs with
    | Some cur_mr =>
      let check_ptr  := check_mem_aux2 cur_mr perm addr chunk in
        match cmp_ptr32_null m check_ptr with
        | Some is_null =>
          if is_null then
            check_mem_aux n mrs_num perm chunk addr mrs m
          else
            Some check_ptr
        | None => None
        end
    | None => None
    end
  end.

Definition check_mem (perm: permission) (chunk: memory_chunk) (addr: val) (mrs_num: nat) (mrs: MyMemRegionsType) (m: mem): option val :=
  match check_mem_aux mrs_num mrs_num perm chunk addr mrs m with
  | Some check_ptr =>
    match cmp_ptr32_null m check_ptr with
    | Some is_null =>
      if is_null then
        Some Vnullptr
      else
        Some check_ptr
    | None => None
    end
  | None => None
  end.

Definition load_mem (chunk: memory_chunk) (ptr: val) (m: mem): option val :=
  match chunk with
  | Mint8unsigned | Mint16unsigned | Mint32 =>
    match Mem.loadv chunk m ptr with
    | Some Vundef => None
    | Some res =>
      match res with
      | Vint v => Some (Vint v)
      | _ => None
      end
    | None => None
    end
  | _ => None
  end.

Definition step_load_x_operation (chunk: memory_chunk) (d:reg) (s:reg) (ofs:off) (rs: regmap) (mrs_num: nat) (mrs: MyMemRegionsType) (m: mem): option (regmap * bpf_flag) :=
  let sv    := eval_regmap s rs in
  let addr  := Val.add sv (sint32_to_vint ofs) in
    match check_mem Readable chunk addr mrs_num mrs m with
    | None => None
    | Some ptr =>
      match cmp_ptr32_null m ptr with
      | None => None
      | Some is_null =>
        if is_null then
          Some (rs, BPF_ILLEGAL_MEM)
        else
          match load_mem chunk ptr m with
          | None => None
          | Some v =>
            let rs' := upd_regmap d v rs in
              Some (rs', BPF_OK)
          end
      end
    end.

Definition store_mem (ptr: val) (chunk: memory_chunk) (v: val) (m: mem): option mem :=
  match chunk with
  | Mint8unsigned | Mint16unsigned | Mint32 =>
    let src := vint_to_vint chunk v in
      Mem.storev chunk m ptr src
  | _ => None
  end.

Definition step_store_operation (chunk: memory_chunk) (d: reg) (s: reg+imm) (ofs: off) (rs: regmap) (mrs_num: nat) (mrs: MyMemRegionsType) (m: mem): option (mem * bpf_flag) :=
  let dv   := eval_regmap d rs in
  let addr := Val.add dv (sint32_to_vint ofs) in
    match s with
    | inl r =>
      let src := eval_regmap r rs in
        match check_mem Writable chunk addr mrs_num mrs m with
        | None => None
        | Some ptr =>
          match cmp_ptr32_null m ptr with
          | None => None
          | Some is_null =>
            if is_null then
              Some (m, BPF_ILLEGAL_MEM)
            else
              match store_mem ptr chunk src m with
              | None => None
              | Some m' => Some (m', BPF_OK)
              end
          end
        end
    | inr i =>
      match check_mem Writable chunk addr mrs_num mrs m with
      | None => None
      | Some ptr =>
        match cmp_ptr32_null m ptr with
        | None => None
        | Some is_null =>
          if is_null then
            Some (m, BPF_ILLEGAL_MEM)
          else
            match store_mem ptr chunk (sint32_to_vint i) m with
            | None => None
            | Some m' => Some (m', BPF_OK)
            end
        end
      end
    end.

Definition eval_ins (pc: int)(l: list int64) (len: nat): option int64 :=
  if (Int.cmpu Clt pc (Int.repr (Z.of_nat len))) then
    List.nth_error l (Z.to_nat (Int.unsigned pc))
  else
    None.


Axiom _bpf_get_call : val -> val.

Axiom exec_function : val -> val.

Definition step (pc: int) (l: list int64) (kv: list nat) (len: nat) (rs: regmap) (mrs_num: nat) (mrs: MyMemRegionsType) (m: mem):
  option (int * regmap * mem * bpf_flag) :=
  match eval_ins pc l len with
  | None => None
  | Some ins64 =>
    match decode ins64 with
    | None => None
    | Some ins =>
      match ins with
      | BPF_NEG d =>
        match jit_call_simpl kv pc rs m with
        | None => None
        | Some (pc', rs', m') => Some (pc', rs', m', BPF_OK)
        end
      | BPF_BINARY bop d s =>
        match jit_call_simpl kv pc rs m with
        | None => None
        | Some (pc', rs', m') => Some (pc', rs', m', BPF_OK)
        end

      | BPF_JA ofs => Some (Int.add pc ofs, rs, m, BPF_OK)
      | BPF_JUMP c d s ofs =>
        let cond := step_branch_cond c d s rs in
          if cond then
            Some (Int.add pc ofs, rs, m, BPF_OK)
          else
            Some (pc, rs, m, BPF_OK)

      | BPF_LDX chunk d s ofs =>
        match step_load_x_operation chunk d s ofs rs mrs_num mrs m with
        | None => None
        | Some (rs', f) => Some (pc, rs', m, f)
        end
      | BPF_ST chunk d s ofs =>
        match step_store_operation chunk d s ofs rs mrs_num mrs m with
        | None => None
        | Some (m, f) => Some (pc, rs, m, f)
        end

      | BPF_CALL i =>
        let f_ptr := _bpf_get_call (Vint ((Int.repr (Int.signed i)))) in
          match cmp_ptr32_null m f_ptr with
          | None => None
          | Some is_null =>
            if is_null then
              Some (pc, rs, m, BPF_ILLEGAL_CALL)
            else
              let res := exec_function f_ptr in
                Some (pc, upd_regmap R0 res rs, m , BPF_OK)
          end
      | BPF_RET    => Some (pc, rs, m, BPF_SUCC_RETURN)
      | BPF_ERR    => Some (pc, rs, m, BPF_ILLEGAL_INSTRUCTION)
      end
    end
  end.

Fixpoint bpf_interpreter_aux (fuel: nat) (pc: int) (l: list int64) (len: nat) (kv: list nat)
  (rs: regmap) (mrs_num: nat) (mrs: MyMemRegionsType) (m: mem) {struct fuel}: option (int * regmap * mem * bpf_flag) :=
  match fuel with
  | O => Some (pc, rs, m, BPF_ILLEGAL_LEN)
  | S fuel0 =>
    if Int.cmpu Clt pc (Int.repr (Z.of_nat len)) then
      match step pc l kv len rs mrs_num mrs m with
      | None => None
      | Some (pc', rs', m' ,f') =>
        if flag_eq f' BPF_OK then
          if Int.cmpu Clt (Int.add pc' Int.one) (Int.repr (Z.of_nat len)) then
            bpf_interpreter_aux fuel0 (Int.add pc' Int.one) l len kv rs' mrs_num mrs m'
          else
            Some (pc', rs', m', BPF_ILLEGAL_LEN)
        else
          Some (pc', rs', m', f')
      end
    else
      Some (pc, rs, m, BPF_ILLEGAL_LEN)
  end.

Definition bpf_interpreter (fuel: nat) (ctx_ptr: val) (pc: int) (l: list int64) (len: nat)
   (kv: list nat) (rs: regmap) (mrs_num: nat) (mrs: MyMemRegionsType) (m: mem): option (val * int * regmap * mem * bpf_flag) :=
  let rs1 := upd_regmap R1 ctx_ptr rs in
    match bpf_interpreter_aux fuel pc l len kv rs1 mrs_num mrs m with
    | None => None
    | Some (pc', rs', m' ,f') =>
      if flag_eq f' BPF_SUCC_RETURN then
        Some (eval_regmap R0 rs', pc', rs', m', f')
      else
        Some (Vzero, pc', rs', m', f')
    end.