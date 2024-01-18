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

From Coq Require Import List ZArith.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values.
From compcert.lib Require Import Integers.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Bool Nat.

From bpf.comm Require Import ListAsArray.
From bpf.dxcomm Require Import CoqIntegers.

(** Coq2C: Values.val -> unsigned long long or unsigned int
  *)

Definition list64AsArrayCompilableType :=
  MkCompilableType List64AsArray.t C_U64_pointer.

Definition list16CompilableType :=
  MkCompilableType List16.t C_U16_pointer.

Definition list32CompilableType :=
  MkCompilableType List32.t C_U32_pointer.

Definition listNatCompilableType :=
  MkCompilableType ListNat.t C_U32_pointer.

Module Exports.
  Definition list64AsArrayCompilableType  := list64AsArrayCompilableType.
  Definition list16CompilableType         := list16CompilableType.
  Definition list32CompilableType         := list32CompilableType.
  Definition listNatCompilableType        := listNatCompilableType.
End Exports.
