From compcert.common Require Import Memory Values AST.
From compcert.lib Require Import Integers.
From compcert.arm Require Import ABinSem.

From bpf.comm Require Import ListAsArray Flag Regs MemRegion rBPFAST JITCall.
From bpf.rbpf32 Require Import TSSyntax.
From bpf.jit Require Import ListSetRefinement KeyValue2.

From Coq Require Import List ZArith.
Import ListNotations.

Definition rbpf_reg_to_tsreg (r: reg): breg :=
  match r with
  | Regs.R0 => R0
  | Regs.R1 => R1
  | Regs.R2 => R2
  | Regs.R3 => R3
  | Regs.R4 => R4
  | Regs.R5 => R5
  | Regs.R6 => R6
  | Regs.R7 => R7
  | Regs.R8 => R8
  | Regs.R9 => R9
  | Regs.R10 => R10
  end.

(** This module defines the jit state *)


Record jit_state := {
  input_len       : nat;
  input_ins       : List64AsArray.t;(**r rBPF binary instructions *)

  tp_kv           : ListKeyV.t; (**r the length of kv2 = the jit_ins_len *)
  use_IR11        : bool; (**r will use IR11 *)

  ld_set          : listset_regmap;
  st_set          : listset_regmap;
(*
  offset          : nat;  (**r the current offset of jitted code *) *)
  tp_bin_len      : nat;  (**r the number of all jitted instructions *)
  tp_bin          : List32.t;

  jit_mem         : mem;
}.

Definition empty_jit_state := {|
  input_len       := 0;
  input_ins       := [];

  tp_kv           := [];
  use_IR11        := false;

  ld_set          := init_listset_regmap;
  st_set          := init_listset_regmap;
(*
  offset          := 0; *)
  tp_bin_len      := 0;
  tp_bin          := List32.create_int_list JITTED_LIST_MAX_LENGTH;

  jit_mem         := Mem.empty
|}.

Definition eval_jit_mem (st: jit_state): Mem.mem := jit_mem st.

Definition upd_jit_mem (m: Mem.mem) (st: jit_state): jit_state := {|
  input_len       := input_len st;
  input_ins       := input_ins st;

  tp_kv           := tp_kv st;
  use_IR11        := use_IR11 st;

  ld_set          := ld_set  st;
  st_set          := st_set  st;
(*
  offset          := offset st;*)
  tp_bin_len      := tp_bin_len st;
  tp_bin          := tp_bin st;
  jit_mem         := m;
|}.

Definition eval_input_len (st: jit_state): nat := (input_len st).

Definition eval_input_ins (pc: nat) (st: jit_state): option int64 := List64AsArray.index (input_ins st) pc.

Definition add_key_value (pc: nat) (v0 v1: nat) (st: jit_state):  jit_state :=
  let kv := {| arm_ofs := v0; alu32_ofs := v1 |} in
  {|
    input_len       := input_len st;
    input_ins       := input_ins st;

    tp_kv           := ListKeyV.assign (tp_kv st) pc kv;
    use_IR11        := use_IR11 st;

    ld_set          := ld_set  st;
    st_set          := st_set  st;
(*
    offset          := offset st; *)
    tp_bin_len      := tp_bin_len st;
    tp_bin          := tp_bin st;
    jit_mem         := jit_mem st;
  |}.

Definition upd_IR11_jittedthumb (f: bool) (st: jit_state):  jit_state :=
  {|
    input_len       := input_len st;
    input_ins       := input_ins st;

    tp_kv           := tp_kv st;
    use_IR11        := f;

    ld_set          := ld_set  st;
    st_set          := st_set  st;
(*
    offset          := offset st; *)
    tp_bin_len      := tp_bin_len st;
    tp_bin          := tp_bin st;
    jit_mem         := jit_mem st;
  |}.

Definition add_jited_bin (ins: int) (st: jit_state): jit_state := {|
  input_len       := input_len st;
  input_ins       := input_ins st;

  tp_kv           := tp_kv st;
  use_IR11        := use_IR11 st;

  ld_set          := ld_set  st;
  st_set          := st_set  st;
(*
  offset          := S (offset st); *)
  tp_bin_len      := S (tp_bin_len st);
  tp_bin          := List32.assign (tp_bin st) (tp_bin_len st) ins;
  jit_mem         := jit_mem st;
|}.

Definition eval_load_regset (r: reg) (st: jit_state): bool :=
  eval_listset_regmap (rbpf_reg_to_tsreg r) (ld_set st).

Definition eval_store_regset (r: reg) (st: jit_state): bool :=
  eval_listset_regmap (rbpf_reg_to_tsreg r) (st_set st).

Definition upd_load_regset (r: reg) (st: jit_state): jit_state := {|
  input_len       := input_len st;
  input_ins       := input_ins st;

  tp_kv           := tp_kv st;
  use_IR11        := use_IR11 st;

  ld_set          := upd_listset_regmap (rbpf_reg_to_tsreg r) (ld_set st);
  st_set          := st_set  st;
(*
  offset          := offset st; *)
  tp_bin_len      := tp_bin_len st;
  tp_bin          := tp_bin st;
  jit_mem         := jit_mem st;
|}.

Definition upd_store_regset (r: reg) (st: jit_state): jit_state := {|
  input_len       := input_len st;
  input_ins       := input_ins st;

  tp_kv           := tp_kv st;
  use_IR11        := use_IR11 st;

  ld_set          := ld_set st;
  st_set          := upd_listset_regmap (rbpf_reg_to_tsreg r) (st_set st);
(*
  offset          := offset st; *)
  tp_bin_len      := tp_bin_len st;
  tp_bin          := tp_bin st;
  jit_mem         := jit_mem st;
|}.

Definition reset_init_jittedthumb (st: jit_state): jit_state := {|
  input_len       := input_len st;
  input_ins       := input_ins st;

  tp_kv           := tp_kv st;
  use_IR11        := false;

  ld_set          := init_listset_regmap;
  st_set          := init_listset_regmap;
(*
  offset          := offset st; *)
  tp_bin_len      := tp_bin_len st;
  tp_bin          := tp_bin st;
  jit_mem         := jit_mem st;
|}.