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

From compcert Require Import AST Integers Values Memory.

From bpf.comm Require Import Regs BinrBPF Flag rBPFValues MemRegion Monad ListAsArray.
From bpf.dxcomm Require Import DxIntegers DxValues.
From bpf.dxmodel Require Import DxRegs DxFlag DxMemRegion.

From bpf.jit.havm Require Import HAVMState.
From Coq Require Import ZArith.

Definition M (A: Type) := Monad.M hybrid_state A.
Definition returnM {A: Type} (a: A) : M A := Monad.returnM a.
Definition bindM {A B: Type} (x: M A) (f: A -> M B) : M B := Monad.bindM x f.

Definition check_pc: M bool := fun st => Some (check_pc st, st).

Definition check_pc_incr: M bool := fun st => Some (check_pc_incr st, st).

Definition upd_pc (p: int): M unit := fun st =>
  if Int.cmpu Cle (Int.add (pc_loc st) p) (Int.sub (Int.repr (Z.of_nat (input_len st))) Int.one) then
    Some (tt, upd_pc p st)
  else (**r TODO: bpf verifier / verifier-invariant should ensure this branch is unreachable *)
    None.

Definition eval_flag: M bpf_flag := fun st => Some (eval_flag st, st).
Definition upd_flag (f:bpf_flag) : M unit := fun st => Some (tt, upd_flag f st).

Definition eval_reg (r: reg) : M valu32_t := fun st => Some (eval_reg r st, st).
Definition upd_reg (r: reg) (v: valu32_t) : M unit := fun st =>
  match v with
  | Vint _ => Some (tt, upd_reg r v st)
  | _ => None
  end.

Definition eval_mrs_num: M nat := fun st => Some (eval_mem_num st, st).

Definition eval_mrs_regions : M MyMemRegionsType := fun st => Some (eval_mem_regions st, st).

Definition eval_mem_regions: M MyMemRegionsType := fun st => Some (eval_mem_regions st, st).

Definition eval_mem : M Mem.mem := fun st => Some (eval_mem st, st).

Definition load_mem (chunk: memory_chunk) (ptr: valu32_t): M valu32_t := fun st => 
  match load_mem chunk ptr st with
  | Some res =>
    match res with
    | Vundef => None
    | _ => Some (res, st)
    end
  | None => None
  end.

Definition store_mem (ptr: valptr8_t) (chunk: memory_chunk) (v: vals32_t) : M unit := fun st =>
  match store_mem ptr chunk v st with
  | Some res => Some (tt, res)
  | None => None
  end.

Definition eval_ins: M int64 := fun st =>
  if (Int.cmpu Clt (pc_loc st) (Int.repr (Z.of_nat (input_len st)))) then
    match eval_ins st with
    | Some i => Some (i, st)
    | None => None
    end
  else (**r TODO: if bpf verifier / verifier-invariant guarantees upd_pc*, we should infer it *)
    None.

Definition cmp_ptr32_nullM (v: valptr8_t): M bool := fun st =>
  match cmp_ptr32_null (HAVMState.eval_mem st) v with
  | Some res => Some (res, st)
  | None     => None (**r TODO: we should infer this *)
  end.

Definition int64_to_dst_reg (ins: int64): M reg := fun st =>
  match int64_to_dst_reg' ins with
  | Some r => Some (r, st)
  | None => None (**r TODO: bpf verifier / verifier-invariant should ensure this branch is unreachable *)
  end.

Definition int64_to_src_reg (ins: int64): M reg := fun st =>
  match int64_to_src_reg' ins with
  | Some r => Some (r, st)
  | None => None (**r TODO: bpf verifier / verifier-invariant should ensure this branch is unreachable *)
  end.

Definition get_mem_region (n:nat) (mrs: MyMemRegionsType): M memory_region := fun st =>
  if (Nat.ltb n (mrs_num st)) then
    match List.nth_error mrs n with
    | Some mr => Some (mr, st)
    | None => None (**r TODO: we should infer this *)
    end
  else
    None.

Definition jit_call: M unit := fun st =>
  match jit_call st with
  | None => None
  | Some st1 => Some (tt, st1)
  end.

(* Given the immediate of the call, it returns a function pointer *)

(* Let assume there is a bpf context pointer in the memory. For the time being, your interpreter does not use it.
   Let keep it that way -- at least for the moment. *)
Axiom _bpf_get_call : vals32_t -> M valptr8_t. (**r here is Vint -> Vptr *)

Axiom exec_function : valptr8_t -> M valu32_t. (**r Vptr -> Vint *)
Axiom lemma_bpf_get_call :
  forall i st1,
    exists ptr,
      _bpf_get_call (Vint i) st1 = Some (ptr, st1) /\
      (ptr = Vnullptr \/ (exists b ofs, ptr = Vptr b ofs /\ ((Mem.valid_pointer (bpf_m st1) b (Ptrofs.unsigned ofs)
        || Mem.valid_pointer (bpf_m st1) b (Ptrofs.unsigned ofs - 1)) = true)%bool)).
Axiom lemma_exec_function0 :
  forall b ofs st1,
      exists v st2, exec_function (Vptr b ofs) st1 = Some (Vint v, st2) /\ cmp_ptr32_null (HAVMState.eval_mem st1) (Vptr b ofs) = Some false.

Declare Scope monad_scope.
Notation "'do' x <-- a ; b" :=
  (bindM a (fun x => b))
    (at level 200, x name, a at level 100, b at level 200)
  : monad_scope.
