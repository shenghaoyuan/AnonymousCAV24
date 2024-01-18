From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values Memory AST.
From compcert.lib Require Import Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Bool Nat.

From bpf.dxcomm Require Import CoqIntegers DxIntegers DxValues.
From bpf.dxmodel Require Import DxFlag DxRegs DxMemRegion.

From bpf.jit.havm Require Import HAVMIdDef HAVMState.

From Coq Require Import List ZArith.
Import ListNotations.

(******************** Dx Related *******************)

Definition state_struct_type: Ctypes.type := Ctypes.Tstruct havm_state_id Ctypes.noattr.

Definition state_struct_def: Ctypes.composite_definition := 
  Ctypes.Composite havm_state_id Ctypes.Struct
    [ Ctypes.Member_plain regs_st_id C_regmap;
      Ctypes.Member_plain pc_loc_id C_U32;
      Ctypes.Member_plain flag_id C_S32;
      Ctypes.Member_plain mrs_num_id C_U32;
      Ctypes.Member_plain mem_region_id mem_region_type;
      Ctypes.Member_plain input_len_id C_U32;
      Ctypes.Member_plain input_ins_id C_U64_pointer;
      Ctypes.Member_plain tp_kv_id C_U32_pointer;
      Ctypes.Member_plain tp_bin_len_id C_U32;
      Ctypes.Member_plain tp_bin_id C_U32_pointer
    ] Ctypes.noattr.

Definition stateCompilableType := MkCompilableType hybrid_state state_struct_type.

Module Exports.
  Definition stateCompilableType := stateCompilableType.
End Exports.
