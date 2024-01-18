From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values Memory AST.
From compcert.lib Require Import Integers.
From compcert.arm Require Import ABinSem.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Bool Nat.

From bpf.comm Require Import ListAsArray Flag Regs MemRegion rBPFAST.
From bpf.dxcomm Require Import CoqIntegers DxIntegers DxValues.
From bpf.dxmodel Require Import DxMemRegion IdentDef.

From bpf.jit Require Import ListSetRefinement.
From bpf.jit.jitcompiler Require Import JITState JITIdDef DxListSetRefinement.

From Coq Require Import List ZArith.
Import ListNotations.

Definition jit_state_type: Ctypes.type := Ctypes.Tpointer (Ctypes.Tstruct jit_state_id Ctypes.noattr) Ctypes.noattr.

Definition jit_state_def: Ctypes.composite_definition := 
  Ctypes.Composite jit_state_id Ctypes.Struct
    [ Ctypes.Member_plain pc_loc_id           C_U32;
      Ctypes.Member_plain input_len_id        C_U32;
      Ctypes.Member_plain input_ins_id        C_U64_pointer;

      Ctypes.Member_plain tp_kv_id            C_U32_pointer;

      Ctypes.Member_plain ld_set_id           C_listset_regmap;
      Ctypes.Member_plain st_set_id           C_listset_regmap;

      Ctypes.Member_plain tp_bin_len_id       C_U32;
      Ctypes.Member_plain tp_bin_id           C_U32_pointer
    ] Ctypes.noattr.

Definition jit_stateCompilableType := MkCompilableType jit_state jit_state_type.

Module Exports.
  Definition jit_stateCompilableType := jit_stateCompilableType.
End Exports.
