From compcert.common Require Import AST Values Memory.
From compcert.lib Require Import Integers.
From compcert.arm Require Import AsmSyntax.

From bpf.comm Require Import Regs BinrBPF Flag rBPFValues MemRegion Monad JITCall.
From bpf.jit Require Import ListSetRefinement JITState.
From Coq Require Import ZArith List.
Import ListNotations.

Definition M (A: Type) := Monad.M jit_state A.
Definition returnM {A: Type} (a: A) : M A := Monad.returnM a.
Definition bindM {A B: Type} (x: M A) (f: A -> M B) : M B := Monad.bindM x f.

Definition eval_jit_mem : M Mem.mem := fun st => Some (eval_jit_mem st, st).

Definition eval_input_len : M nat := fun st => Some (eval_input_len st, st).

Definition eval_input_ins (pc: nat) : M int64 := fun st =>
  if (Int.cmpu Clt (Int.repr (Z.of_nat pc)) (Int.repr (Z.of_nat (input_len st)))) then
    match eval_input_ins pc st with
    | Some ins => Some (ins, st)
    | None => None
    end
  else (**r TODO: if bpf verifier / verifier-invariant guarantees upd_pc*, we should infer it *)
    None.

Definition get_dst (ins: int64): M reg := fun st =>
  match int64_to_dst_reg' ins with
  | Some r => Some (r, st)
  | None => None (**r TODO: bpf verifier / verifier-invariant should ensure this branch is unreachable *)
  end.

Definition get_src (ins: int64): M reg := fun st =>
  match int64_to_src_reg' ins with
  | Some r => Some (r, st)
  | None => None (**r TODO: bpf verifier / verifier-invariant should ensure this branch is unreachable *)
  end.

Definition eval_arm_ofs: M nat := fun st => Some(tp_bin_len st, st).

Definition add_key_value (pc: nat) (v0 v1: nat): M unit := fun st =>
  Some (tt, add_key_value pc v0 v1 st).

Definition eval_use_IR11: M bool := fun st => Some(use_IR11 st, st).

Definition upd_IR11_jittedthumb (f: bool): M unit := fun st =>
  Some (tt, upd_IR11_jittedthumb f st).

Definition add_jited_bin (ins: int): M unit := fun st =>
  if Nat.ltb (tp_bin_len st) JITTED_LIST_MAX_LENGTH then
    Some (tt, add_jited_bin ins st)
  else (**r TODO: give an error flag *)
    None.

Definition eval_load_regset (r: reg): M bool := fun st =>
  Some (eval_load_regset r st, st).

Definition eval_store_regset (r: reg): M bool := fun st =>
  Some (eval_store_regset r st, st).

Definition upd_load_regset (r: reg): M unit := fun st =>
  Some (tt, upd_load_regset r st).

Definition upd_store_regset (r: reg): M unit := fun st =>
  Some (tt, upd_store_regset r st).

Definition reset_init_jittedthumb: M unit := fun st => Some (tt, reset_init_jittedthumb st).

Declare Scope monad_scope.
Notation "'do' x <-- a ; b" :=
  (bindM a (fun x => b))
    (at level 200, x name, a at level 100, b at level 200)
  : monad_scope.