From compcert Require Import Integers Memory AST Ctypes.
From Coq Require Import ZArith Ascii String HexString List.

From bpf.rbpf32 Require Import TSDecode TSPrint.
From bpf.jit Require Import ThumbDecode PrintThumb.

Import ListNotations.

(** This module is used for printing jitted arm32 code *)

Record jit_state_string :={
  ibpf_string   : list string;
  jitted_len_nat: nat;
  jitted_string : list string
}.

Definition print_jit_state (l: list int64) (l1: list int) (phyical_start_addr: int): jit_state_string := {|
  ibpf_string     := print_rBPF_prog (decode_prog l (List.length l));
  jitted_len_nat  := List.length l1;
  jitted_string   := print_arm32_prog (arm32_decode_prog l1) phyical_start_addr;
|}.