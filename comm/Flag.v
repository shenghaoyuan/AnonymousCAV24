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
From compcert.lib Require Import Integers.
From compcert.common Require Import Values.
Import ListNotations.

Inductive bpf_flag: Type := 
  | BPF_SUCC_RETURN         (**r =  1, *)
  | BPF_OK                  (**r =  0, *)
  | BPF_ILLEGAL_INSTRUCTION (**r =  2, *)
  | BPF_ILLEGAL_MEM         (**r =  3, *)
  | BPF_ILLEGAL_JUMP        (**r =  4, *)
  | BPF_ILLEGAL_CALL        (**r =  5, *)
  | BPF_ILLEGAL_LEN         (**r =  6, *)
  | BPF_ILLEGAL_REGISTER    (**r =  7, *)
  | BPF_NO_RETURN           (**r =  8, *)
  | BPF_OUT_OF_BRANCHES     (**r =  9, *)
  | BPF_ILLEGAL_DIV         (**r = 10, *)
  | BPF_ILLEGAL_SHIFT       (**r = 11, *)
  | BPF_ILLEGAL_ARM_RANGE   (**r = 12, *)
  | BPF_ILLEGAL_JIT         (**r = 13, *)
  | BPF_ILLEGAL_ARM_LEN     (**r = 14, *)
  | BPF_ILLEGAL_EP_LEN      (**r = 15, *)
.
Lemma bpf_flag_eq: forall (x y: bpf_flag), {x=y} + {x<>y}.
Proof.
decide equality. Defined.

(** flag_eq: flag -> flag -> bool
  *)
Definition flag_eq (x y: bpf_flag): bool :=
  match x, y with
  | BPF_SUCC_RETURN, BPF_SUCC_RETURN
  | BPF_OK, BPF_OK
  | BPF_ILLEGAL_INSTRUCTION, BPF_ILLEGAL_INSTRUCTION
  | BPF_ILLEGAL_MEM, BPF_ILLEGAL_MEM
  | BPF_ILLEGAL_JUMP, BPF_ILLEGAL_JUMP
  | BPF_ILLEGAL_CALL, BPF_ILLEGAL_CALL
  | BPF_ILLEGAL_LEN, BPF_ILLEGAL_LEN
  | BPF_ILLEGAL_REGISTER, BPF_ILLEGAL_REGISTER
  | BPF_NO_RETURN, BPF_NO_RETURN
  | BPF_OUT_OF_BRANCHES, BPF_OUT_OF_BRANCHES
  | BPF_ILLEGAL_DIV, BPF_ILLEGAL_DIV
  | BPF_ILLEGAL_SHIFT, BPF_ILLEGAL_SHIFT
  | BPF_ILLEGAL_ARM_RANGE, BPF_ILLEGAL_ARM_RANGE
  | BPF_ILLEGAL_JIT, BPF_ILLEGAL_JIT
  | BPF_ILLEGAL_ARM_LEN, BPF_ILLEGAL_ARM_LEN
  | BPF_ILLEGAL_EP_LEN, BPF_ILLEGAL_EP_LEN => true
  | _, _ => false
  end.

Definition Z_of_flag (f:bpf_flag) : Z :=
  match f with
  | BPF_SUCC_RETURN  => 1
  | BPF_OK  => 0
  | BPF_ILLEGAL_INSTRUCTION => 2
  | BPF_ILLEGAL_MEM => 3
  | BPF_ILLEGAL_JUMP => 4
  | BPF_ILLEGAL_CALL => 5
  | BPF_ILLEGAL_LEN  => 6
  | BPF_ILLEGAL_REGISTER => 7
  | BPF_NO_RETURN => 8
  | BPF_OUT_OF_BRANCHES => 9
  | BPF_ILLEGAL_DIV => 10
  | BPF_ILLEGAL_SHIFT => 11
  | BPF_ILLEGAL_ARM_RANGE => 12
  | BPF_ILLEGAL_JIT => 13
  | BPF_ILLEGAL_ARM_LEN => 14
  | BPF_ILLEGAL_EP_LEN => 15
  end.

Definition int_of_flag (f:bpf_flag)  :=
  Int.repr (Z_of_flag f).

Definition val_of_flag (f:bpf_flag)  :=
  Vint (Int.repr (Z_of_flag f)).