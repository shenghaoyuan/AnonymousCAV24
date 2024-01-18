From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values Memory.
From compcert.lib Require Import Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Bool Nat.

From bpf.comm Require Import Regs.
From bpf.dxcomm Require Import CoqIntegers DxIntegers DxValues.
From bpf.dxmodel Require Import DxRegs.
From bpf.jit Require Import ListSetRefinement.

From Coq Require Import List ZArith.
Import ListNotations.

Definition C_listset_regmap: Ctypes.type := Ctypes.Tarray Ctypes.type_bool 11%Z Ctypes.noattr.

Definition listset_regmapCompilableType := MkCompilableType listset_regmap C_listset_regmap.

Module Exports.
  Definition listset_regmapCompilableType  := listset_regmapCompilableType.
End Exports.