From compcert.common Require Import AST Memory.
From compcert.lib Require Import Integers.
From compcert.arm Require Import AsmSyntax.

From bpf.comm Require Import Monad Flag Regs MemRegion JITCall.
From bpf.dxcomm Require Import DxIntegers DxValues.
From bpf.dxmodel Require Import DxRegs DxFlag DxMemRegion.

From bpf.jit Require Import ListSetRefinement.
From bpf.jit.jitcompiler Require Import JITState JITMonadOp.

Definition eval_input_len : M nat := JITMonadOp.eval_input_len.

(**r here we must use sint32_t instead of int because pc is signed int *)
Definition eval_input_ins (pc: nat): M int64 := JITMonadOp.eval_input_ins pc.

Definition get_dst (ins: int64): M reg := int64_to_dst_reg ins.

Definition get_src (ins: int64): M reg := int64_to_src_reg ins.

Definition add_key_value (pc: nat): M unit := JITMonadOp.add_key_value pc.

Definition add_jited_bin (ins: int): M unit := JITMonadOp.add_jited_bin ins.

Definition eval_load_regset (r: reg): M bool := JITMonadOp.eval_load_regset r.

Definition eval_store_regset (r: reg): M bool := JITMonadOp.eval_store_regset r.

Definition upd_load_regset (r: reg): M unit := JITMonadOp.upd_load_regset r.

Definition upd_store_regset (r: reg): M unit := JITMonadOp.upd_store_regset r.

Definition reset_init_jittedthumb: M unit := JITMonadOp.reset_init_jittedthumb.
