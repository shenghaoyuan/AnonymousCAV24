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

From Coq Require Import BinNums List Ascii String Nat ZArith.
From Coq Require Import Numbers.AltBinNotations.
Import List.ListNotations.

From compcert.cfrontend Require Csyntax Ctypes.
From compcert.common Require Import Errors Values.
From compcert.lib Require Import Integers.

From dx Require Import ResultMonad IR CoqIR IRtoC DXModule DumpAsC.
From dx.Type Require Bool Nat.

From bpf.dxcomm Require Import DxIntegers DxValues DxBinrBPF DxNat.
From bpf.dxmodel Require Import DxFlag DxRegs DxMemRegion DxMemType DxAST DxOpcode.
From bpf.jit.jitcompiler Require Import DxMonadCommon DxKeyValue2.
From bpf.jit.havm Require Import HAVMIdDef DxHAVMState HAVMMonadOp DxHAVMInterpreter.

(***************************************)

GenerateIntermediateRepresentation SymbolIRs
  M bindM returnM
  Bool.Exports
  Nat.Exports
  DxIntegers.Exports
  DxValues.Exports
  DxRegs.Exports
  DxBinrBPF.Exports
  DxFlag.Exports
  DxAST.Exports
  DxOpcode.Exports
  DxMemRegion.Exports
  DxMemType.Exports
  DxNat.Exports
  DxKeyValue2.Exports
  check_pc
  check_pc_incr
  upd_pc
  eval_flag
  upd_flag
  eval_reg
  upd_reg
  eval_mrs_num
  eval_mrs_regions
  eval_mem_regions
  load_mem
  store_mem
  eval_ins
  cmp_ptr32_nullM
  get_dst
  get_src
  jit_call
  get_mem_region
  _bpf_get_call
  exec_function (**r hybrid_state *)
  __
  get_offset
  get_immediate
  get_src32
  get_opcode_ins
  get_opcode_alu32
  get_opcode_branch
  get_opcode_mem_ld_reg
  get_opcode_mem_st_imm
  get_opcode_mem_st_reg
  get_opcode_nat
  get_add
  get_sub
  get_addr_ofs
  get_start_addr
  get_block_size
  get_block_perm
  check_mem_aux2
  check_mem_aux
  check_mem
  step_opcode_branch
  step_opcode_mem_ld_reg
  step_opcode_mem_st_imm
  step_opcode_mem_st_reg
  step
  bpf_interpreter_aux
  havm_interpreter
.

Open Scope string_scope.

Definition dxModuleTest := makeDXModuleWithUserIds 
  [ mem_region_def; state_struct_def]
  [ "memory_region";
    "start_addr"; "block_size"; "block_perm"; "block_ptr";
    "havm_state";
    "regs_st"; "pc_loc"; "flag"; "mrs_num"; "mrs";
    "input_len"; "input_ins"; "tp_kv"; "tp_bin_len"; "tp_bin" ] SymbolIRs.

Close Scope string_scope.