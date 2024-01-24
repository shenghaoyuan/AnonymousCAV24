From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values Memory AST.
From compcert.lib Require Import Integers.
From compcert.arm Require Import ABinSem.

From bpf.comm Require Import ListAsArray Flag MemRegion rBPFAST rBPFValues JITCall Monad.

From bpf.rbpf32 Require Import TSSyntax BState.

From Coq Require Import List ZArith.
Import ListNotations.

Definition M (A: Type) := Monad.M state A.
Definition returnM {A: Type} (a: A) : M A := Monad.returnM a.
Definition bindM {A B: Type} (x: M A) (f: A -> M B) : M B := Monad.bindM x f.

Definition eval_cmp (cop: cmpOp) (d: breg) (s: breg+imm): M bool := fun st =>
  match eval_cmp cop d s st with
  | None => None
  | Some cond => Some (cond, st)
  end.

Definition upd_pc (p: val): M unit := fun st => Some (tt, upd_pc p st).

Definition upd_pc_incr: M unit := fun st => Some (tt, (upd_regs (nextinstr (regs_st st)) st)).

Definition eval_flag: M bpf_flag := fun st => Some (flag st, st).

Definition upd_flag (f: bpf_flag): M unit := fun st => Some (tt, upd_flag f st).

Definition upd_regs (rs: regset): M unit := fun st => Some (tt, upd_regs rs st).

Definition eval_reg (r: breg): M val := fun st => Some (eval_reg r st, st).

Definition upd_reg (r: breg) (v:val): M unit := fun st =>
  match v with
  | Vint n => Some (tt, upd_reg r v st)
  | _ => None
  end.

Definition eval_mem_num: M nat := fun st => Some (mrs_num st, st).

Definition eval_mem_regions: M MyMemRegionsType := fun st => Some (bpf_mrs st, st).

Definition get_mem_region (n: nat) (mrs: MyMemRegionsType): M memory_region := fun st =>
  match get_mem_region n (mrs_num st) mrs with
  | None => None
  | Some mr => Some (mr, st)
  end.

Definition load_mem (chunk: memory_chunk) (ptr: val): M val := fun st =>
  match load_mem chunk ptr st with
  | None => None
  | Some v => Some (v, st)
  end.

Definition store_mem (ptr: val) (chunk: memory_chunk) (v: val): M unit := fun st =>
  match store_mem ptr chunk v st with
  | None => None
  | Some m => Some (tt, m)
  end.

Definition eval_ins_len: M int := fun st => Some (eval_ins_len st, st).

Definition eval_ins: M int64 := fun st =>
  match eval_ins st with
  | None => None
  | Some v => Some (v, st)
  end.

Definition cmp_ptr32_nullM (v: val): M bool := fun st =>
  match cmp_ptr32_null (bpf_m st) v with
  | Some res => Some (res, st)
  | None     => None
  end.

Definition jit_call_simplb: M unit := fun st =>
  match jit_call_simplb (tp_kv st) (regs_st st) (bpf_m st) with
  | None => None
  | Some (rs, m) => Some (tt, BState.upd_mem m (BState.upd_regs rs st))
  end.

Definition _bpf_get_call (id: ident) (sg: signature): M val := fun st =>
  match _bpf_get_call id sg (bpf_m st) with
  | None => None
  | Some (v, m) => Some (v, (BState.upd_mem m st))
  end.