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

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values Memory.
From compcert.lib Require Import Integers.

From bpf.comm Require Import rBPFValues.
From Coq Require Import List ZArith.
Import ListNotations.


Inductive reg: Type :=
  | R0:reg | R1:reg | R2:reg
  | R3:reg | R4:reg | R5:reg
  | R6:reg | R7:reg | R8:reg
  | R9:reg | R10:reg
.

Lemma reg_eq: forall (x y: reg), {x=y} + {x<>y}.
Proof.
decide equality. Defined.

Definition reg_eqb (r0 r1: reg) : bool :=
  match r0, r1 with
  | R0, R0
  | R1, R1
  | R2, R2
  | R3, R3
  | R4, R4
  | R5, R5
  | R6, R6
  | R7, R7
  | R8, R8
  | R9, R9
  | R10, R10 => true
  | _, _ => false
  end.

Lemma reg_eqb_true:
  forall x y, x = y <-> reg_eqb x y = true.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

Lemma reg_eqb_false:
  forall x y, x <> y <-> reg_eqb x y = false.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

Record regmap: Type := make_regmap{
  r0_val  : val;
  r1_val  : val;
  r2_val  : val;
  r3_val  : val;
  r4_val  : val;
  r5_val  : val;
  r6_val  : val;
  r7_val  : val;
  r8_val  : val;
  r9_val  : val;
  r10_val : val;
}.

Definition eval_regmap (r:reg) (regs:regmap): val := 
  match r with
  | R0  => r0_val regs
  | R1  => r1_val regs
  | R2  => r2_val regs
  | R3  => r3_val regs
  | R4  => r4_val regs
  | R5  => r5_val regs
  | R6  => r6_val regs
  | R7  => r7_val regs
  | R8  => r8_val regs
  | R9  => r9_val regs
  | R10 => r10_val regs
  end.

Definition upd_regmap (r:reg) (v:val) (regs:regmap): regmap :=
  match r with
  | R0  => 
    {|
      r0_val  := v;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R1  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := v;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |}
  | R2  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := v;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R3  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := v;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R4  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := v;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R5  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := v;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R6  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := v;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R7  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := v;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R8  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := v;
      r9_val  := r9_val regs;
      r10_val := r10_val regs;
    |} 
  | R9  => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := v;
      r10_val := r10_val regs;
    |} 
  | R10 => 
    {|
      r0_val  := r0_val regs;
      r1_val  := r1_val regs;
      r2_val  := r2_val regs;
      r3_val  := r3_val regs;
      r4_val  := r4_val regs;
      r5_val  := r5_val regs;
      r6_val  := r6_val regs;
      r7_val  := r7_val regs;
      r8_val  := r8_val regs;
      r9_val  := r9_val regs;
      r10_val := v;
    |} 
  end.

(**r the value is 32-bit *)
Definition init_regmap: regmap := {|
  r0_val  := Vzero;
  r1_val  := Vzero;
  r2_val  := Vzero;
  r3_val  := Vzero;
  r4_val  := Vzero;
  r5_val  := Vzero;
  r6_val  := Vzero;
  r7_val  := Vzero;
  r8_val  := Vzero;
  r9_val  := Vzero;
  r10_val := Vzero;
|}.

Definition id_of_reg (r:reg) : Z :=
  match r with
  | R0 => 0
  | R1 => 1
  | R2 => 2
  | R3 => 3
  | R4 => 4
  | R5 => 5
  | R6 => 6
  | R7 => 7
  | R8 => 8
  | R9 => 9
  | R10 => 10
  end.

Definition reg2nat (r: reg): nat :=
  match r with
  | R0 => 0
  | R1 => 1
  | R2 => 2
  | R3 => 3
  | R4 => 4
  | R5 => 5
  | R6 => 6
  | R7 => 7
  | R8 => 8
  | R9 => 9
  | R10 => 10
  end.

Definition int_of_reg (r: reg): int := Int.repr (id_of_reg r).

Definition int16_of_reg (r: reg): int := Int.repr (id_of_reg r).

Lemma eval_upd_reg_same:
  forall r v st,
    eval_regmap r (upd_regmap r v st) = v.
Proof.
  intros.
  unfold eval_regmap, upd_regmap.
  destruct r; reflexivity.
Qed.

Lemma eval_upd_reg_other:
  forall r r0 v st,
    r <> r0 ->
    eval_regmap r (upd_regmap r0 v st) = eval_regmap r st.
Proof.
  intros.
  unfold eval_regmap, upd_regmap.
  destruct r; destruct r0; try reflexivity.
  all: exfalso; apply H; reflexivity.
Qed.

Lemma reg_eqb_refl:
  forall r,
    reg_eqb r r = true.
Proof.
  destruct r; simpl; reflexivity.
Qed.