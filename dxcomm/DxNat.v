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

Require Import List.
Import ListNotations.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert Require Import Integers Values.

From dx Require Import ResultMonad IR.
From dx.Type Require Import Bool Nat.

From bpf.comm Require Import rBPFNat rBPFValues.
From bpf.dxcomm Require Import CoqIntegers DxIntegers.
From Coq Require Import ZArith Number Decimal.

(* Derive Nat as unsigned int *)
(* To ensure soundness, S is not derived as +1, only O is derivable *)
(* One can still provide a primitive encoding for specific constants *)
Open Scope nat_scope.

(**r nat8 *)
Definition nat8 := nat.
Definition nat8_1 := 1.
Definition nat32_1 := 1.

Definition nat8_536870911 := Init.Nat.of_num_uint (UIntDecimal (D5 (D3 (D6 (D8 (D7 (D0 (D9 (D1 (D1 Nil)))))))))).

(** masking operation *)
Definition nat8_0xf0 := 0xf0.
Definition nat8_0x07 := 0x07.
Definition nat8_0xff := 0xff.
Definition nat8_0x08 := 0x08.
Definition nat8_zero := 0x00.

Definition nat8_0x05 := 0x05.
Definition nat8_0x84 := 0x84.
Definition nat8_0x87 := 0x87.
Definition nat8_0x85 := 0x85.
Definition nat8_0x95 := 0x95.

Definition nat8CompilableType :=
  MkCompilableType nat8 C_U8.

Definition C_NAT8_1: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_1))) C_U8.

Definition C_NAT32_1: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat32_1))) C_U32.

(**r masking operations *)
Definition C_NAT8_0xf0: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_0xf0))) C_U8.

Definition C_NAT8_0x07: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_0x07))) C_U8.

Definition C_NAT8_0xff: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_0xff))) C_U8.

Definition C_NAT8_0x08: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_0x08))) C_U8.

Definition C_NAT8_0x00: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_zero))) C_U8.

Definition C_NAT8_0x05: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_0x05))) C_U8.

Definition C_NAT8_0x84: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_0x84))) C_U8.

Definition C_NAT8_0x87: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_0x87))) C_U8.

Definition C_NAT8_0x85: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_0x85))) C_U8.

Definition C_NAT8_0x95: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_0x95))) C_U8.

Definition C_NAT8_536870911: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat nat8_536870911))) C_U8.



Definition nat8SymbolType :=
  MkCompilableSymbolType nil (Some nat8CompilableType).

Definition Const_nat8_1    := constant nat8SymbolType nat8_1    C_NAT8_1.
Definition Const_nat32_1   := constant nat8SymbolType nat32_1   C_NAT32_1.
Definition Const_nat8_0xf0 := constant nat8SymbolType nat8_0xf0 C_NAT8_0xf0.
Definition Const_nat8_0x07 := constant nat8SymbolType nat8_0x07 C_NAT8_0x07.
Definition Const_nat8_0xff := constant nat8SymbolType nat8_0xff C_NAT8_0xff.
Definition Const_nat8_0x08 := constant nat8SymbolType nat8_0x08 C_NAT8_0x08.
Definition Const_nat8_zero := constant nat8SymbolType nat8_zero C_NAT8_0x00.
Definition Const_nat8_0x05 := constant nat8SymbolType nat8_0x05 C_NAT8_0x05.
Definition Const_nat8_0x84 := constant nat8SymbolType nat8_0x84 C_NAT8_0x84.
Definition Const_nat8_0x87 := constant nat8SymbolType nat8_0x87 C_NAT8_0x87.
Definition Const_nat8_0x85 := constant nat8SymbolType nat8_0x85 C_NAT8_0x85.
Definition Const_nat8_0x95 := constant nat8SymbolType nat8_0x95 C_NAT8_0x95.
Definition Const_nat8_536870911 := constant nat8SymbolType nat8_536870911 C_NAT8_536870911.

Definition nat8Tonat8ToboolSymbolType :=
  MkCompilableSymbolType [nat8CompilableType; nat8CompilableType] (Some boolCompilableType).

Definition C_NAT8_eq (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Oeq x y C_U8.

Definition Const_nat8_eq :=
  MkPrimitive nat8Tonat8ToboolSymbolType
                Nat.eqb
                (fun es => match es with
                           | [e1;e2] => Ok (C_NAT8_eq e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition C_NAT8_le (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Ole x y C_U8.

Definition Const_nat8_le :=
  MkPrimitive nat8Tonat8ToboolSymbolType
                Nat.leb
                (fun es => match es with
                           | [e1;e2] => Ok (C_NAT8_le e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).



Definition nat8Tonat8Tonat8SymbolType :=
  MkCompilableSymbolType [nat8CompilableType; nat8CompilableType] (Some nat8CompilableType).

Definition C_NAT8_and (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Oand x y C_U8.

Definition Const_nat8_and :=
  MkPrimitive nat8Tonat8Tonat8SymbolType
                Nat.land
                (fun es => match es with
                           | [e1;e2] => Ok (C_NAT8_and e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition C_NAT8_sub (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Osub x y C_U8.

Definition Const_nat8_sub :=
  MkPrimitive nat8Tonat8Tonat8SymbolType
                Nat.sub
                (fun es => match es with
                           | [e1;e2] => Ok (C_NAT8_sub e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition nat8Touint32SymbolType :=
  MkCompilableSymbolType [nat8CompilableType] (Some uint32CompilableType).

Definition Const_nat2int :=
  MkPrimitive nat8Touint32SymbolType
                nat8_to_int
                (fun es => match es with
                           | [e1] => Ok (e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).

(**r nat32 *)


Definition C_NAT_1: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 1))) C_U32.

Definition C_NAT_2: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 2))) C_U32.

Definition C_NAT_3: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 3))) C_U32.

Definition C_NAT_4: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 4))) C_U32.

Definition C_NAT_5: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 5))) C_U32.

Definition C_NAT_6: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 6))) C_U32.

Definition C_NAT_7: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 7))) C_U32.

Definition C_NAT_8: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 8))) C_U32.

Definition C_NAT_9: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 9))) C_U32.

Definition C_NAT_10: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 10))) C_U32.

Definition C_NAT_11: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 11))) C_U32.

Definition C_NAT_12: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 12))) C_U32.

Definition C_NAT_13: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 13))) C_U32.

Definition C_NAT_14: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 14))) C_U32.

Definition C_NAT_15: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 15))) C_U32.

Definition C_NAT_16: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 16))) C_U32.

Definition C_NAT_17: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 17))) C_U32.

Definition C_NAT_18: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 18))) C_U32.

Definition C_NAT_19: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 19))) C_U32.

Definition C_NAT_20: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 20))) C_U32.

Definition C_NAT_24: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 24))) C_U32.

Definition C_NAT_27: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 27))) C_U32.

Definition C_NAT_28: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 28))) C_U32.

Definition C_NAT_32: Csyntax.expr :=
  Csyntax.Eval (Vint (Int.repr (Z.of_nat 32))) C_U32.

Definition Const_NAT_1        := constant natSymbolType nat_1     C_NAT_1.
Definition Const_NAT_2        := constant natSymbolType nat_2     C_NAT_2.
Definition Const_NAT_3        := constant natSymbolType nat_3     C_NAT_3.
Definition Const_NAT_4        := constant natSymbolType nat_4     C_NAT_4.
Definition Const_NAT_5        := constant natSymbolType nat_5     C_NAT_5.
Definition Const_NAT_6        := constant natSymbolType nat_6     C_NAT_6.
Definition Const_NAT_7        := constant natSymbolType nat_7     C_NAT_7.
Definition Const_NAT_8        := constant natSymbolType nat_8     C_NAT_8.
Definition Const_NAT_9        := constant natSymbolType nat_9     C_NAT_9.
Definition Const_NAT_10       := constant natSymbolType nat_10    C_NAT_10.
Definition Const_NAT_11       := constant natSymbolType nat_11    C_NAT_11.
Definition Const_NAT_12       := constant natSymbolType nat_12    C_NAT_12.
Definition Const_NAT_13       := constant natSymbolType nat_13    C_NAT_13.
Definition Const_NAT_14       := constant natSymbolType nat_14    C_NAT_14.
Definition Const_NAT_15       := constant natSymbolType nat_15    C_NAT_15.
Definition Const_NAT_16       := constant natSymbolType nat_16    C_NAT_16.
Definition Const_NAT_17       := constant natSymbolType nat_17    C_NAT_17.
Definition Const_NAT_18       := constant natSymbolType nat_18    C_NAT_18.
Definition Const_NAT_19       := constant natSymbolType nat_19    C_NAT_19.
Definition Const_NAT_20       := constant natSymbolType nat_20    C_NAT_20.
Definition Const_NAT_24       := constant natSymbolType nat_24    C_NAT_24.
Definition Const_NAT_27       := constant natSymbolType nat_27    C_NAT_27.
Definition Const_NAT_28       := constant natSymbolType nat_28    C_NAT_28.
Definition Const_NAT_32       := constant natSymbolType nat_32    C_NAT_32.

Definition natTouint32SymbolType :=
  MkCompilableSymbolType [natCompilableType] (Some uint32CompilableType).

Definition Const_int_of_nat :=
  MkPrimitive natTouint32SymbolType
                int_of_nat
                (fun es => match es with
                           | [e1] => Ok (e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition natTouint16SymbolType :=
  MkCompilableSymbolType [natCompilableType] (Some uint16CompilableType).

Definition Const_int16_of_nat :=
  MkPrimitive natTouint16SymbolType
                int16_of_nat
                (fun es => match es with
                           | [e1] => Ok (e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition natToint64SymbolType :=
  MkCompilableSymbolType [natCompilableType] (Some int64CompilableType).

Definition Const_int64_of_nat :=
  MkPrimitive natToint64SymbolType
                int64_of_nat
                (fun es => match es with
                           | [e1] => Ok (Csyntax.Ecast e1 C_U64)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition uint32TonatSymbolType :=
  MkCompilableSymbolType [uint32CompilableType] (Some natCompilableType).

Definition Const_nat_of_int :=
  MkPrimitive uint32TonatSymbolType
                nat_of_int
                (fun es => match es with
                           | [e1] => Ok (e1)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition natTonatTonatSymbolType :=
  MkCompilableSymbolType [natCompilableType; natCompilableType] (Some natCompilableType).

Definition C_NAT_add (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Oadd x y C_U32.

Definition Const_nat_add :=
  MkPrimitive natTonatTonatSymbolType
                Nat.add
                (fun es => match es with
                           | [e1;e2] => Ok (C_NAT_add e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition C_NAT_mul (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Omul x y C_U32.

Definition Const_nat_mul :=
  MkPrimitive natTonatTonatSymbolType
                Nat.mul
                (fun es => match es with
                           | [e1;e2] => Ok (C_NAT_mul e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Definition C_NAT_div (x y: Csyntax.expr): Csyntax.expr :=
  Csyntax.Ebinop Cop.Odiv x y C_U32.

Definition Const_nat_div :=
  MkPrimitive natTonatTonatSymbolType
                Nat.div
                (fun es => match es with
                           | [e1;e2] => Ok (C_NAT_div e1 e2)
                           | _       => Err PrimitiveEncodingFailed
                           end).

Module Exports.
  Definition nat8CompilableType := nat8CompilableType.
  Definition Const_nat8_1       := Const_nat8_1.
  Definition Const_nat32_1      := Const_nat32_1.
  Definition Const_nat8_0xf0    := Const_nat8_0xf0.
  Definition Const_nat8_0x07    := Const_nat8_0x07.
  Definition Const_nat8_0xff    := Const_nat8_0xff.
  Definition Const_nat8_0x08    := Const_nat8_0x08.
  Definition Const_nat8_0x05    := Const_nat8_0x05.
  Definition Const_nat8_0x84    := Const_nat8_0x84.
  Definition Const_nat8_0x87    := Const_nat8_0x87.
  Definition Const_nat8_0x85    := Const_nat8_0x85.
  Definition Const_nat8_0x95    := Const_nat8_0x95.
  Definition Const_nat8_zero    := Const_nat8_zero.
  Definition Const_nat8_eq      := Const_nat8_eq.
  Definition Const_nat8_le      := Const_nat8_le.
  Definition Const_nat8_and     := Const_nat8_and.
  Definition Const_nat8_sub     := Const_nat8_sub.
  Definition Const_nat2int      := Const_nat2int.
  Definition Const_nat8_536870911 := Const_nat8_536870911.

  Definition Const_NAT_1        := Const_NAT_1.
  Definition Const_NAT_2        := Const_NAT_2.
  Definition Const_NAT_3        := Const_NAT_3.
  Definition Const_NAT_4        := Const_NAT_4.
  Definition Const_NAT_5        := Const_NAT_5.
  Definition Const_NAT_6        := Const_NAT_6.
  Definition Const_NAT_7        := Const_NAT_7.
  Definition Const_NAT_8        := Const_NAT_8.
  Definition Const_NAT_9        := Const_NAT_9.
  Definition Const_NAT_10       := Const_NAT_10.
  Definition Const_NAT_11       := Const_NAT_11.
  Definition Const_NAT_12       := Const_NAT_12.
  Definition Const_NAT_13       := Const_NAT_13.
  Definition Const_NAT_14       := Const_NAT_14.
  Definition Const_NAT_15       := Const_NAT_15.
  Definition Const_NAT_16       := Const_NAT_16.
  Definition Const_NAT_17       := Const_NAT_17.
  Definition Const_NAT_18       := Const_NAT_18.
  Definition Const_NAT_19       := Const_NAT_19.
  Definition Const_NAT_20       := Const_NAT_20.
  Definition Const_NAT_24       := Const_NAT_24.
  Definition Const_NAT_27       := Const_NAT_27.
  Definition Const_NAT_28       := Const_NAT_28.
  Definition Const_NAT_32       := Const_NAT_32.
  Definition Const_int_of_nat   := Const_int_of_nat.
  Definition Const_int16_of_nat := Const_int16_of_nat.
  Definition Const_int64_of_nat := Const_int64_of_nat.
  Definition Const_nat_of_int   := Const_nat_of_int.
  Definition Const_nat_add      := Const_nat_add.
  Definition Const_nat_mul      := Const_nat_mul.
  Definition Const_nat_div      := Const_nat_div.
End Exports.