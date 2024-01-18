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
From bpf.dxmodel Require Import DxFlag DxRegs DxMemRegion DxMemType DxAST.
From bpf.jit.jitcompiler Require Import JITIdDef DxJITNat DxListSetRefinement DxKeyValue2 DxJITMonadState JITMonadOp DxMonadCommon DxThumbInsOp DxThumbJIT DxThumbJITOpcode.

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
  DxMemRegion.Exports
  DxMemType.Exports
  DxNat.Exports
  DxJITNat.Exports
  DxListSetRefinement.Exports
  DxThumbInsOp.Exports
  DxThumbJITOpcode.Exports
  eval_input_len
  eval_input_ins
  get_dst
  get_src
  eval_arm_ofs
  add_key_value
  eval_use_IR11
  upd_IR11_jittedthumb
  add_jited_bin
  eval_load_regset
  eval_store_regset
  upd_load_regset
  upd_store_regset
  reset_init_jittedthumb (**r jit_state *)
  decode_thumb
  encode_thumb
  ins_is_bpf_alu32
  ins_is_bpf_jump (**r DxThumbJIT *)
  __
  get_immediate
  get_offset
  get_opcode_ins (**r DxMonadCommon *)
  jit_alu32_thumb_mem_template_jit
  jit_alu32_pre
  jit_call_save_add
  jit_call_save_reg
  jit_call_save_imm
  bpf_alu32_to_thumb_reg_comm
  bpf_alu32_to_thumb_reg
  load_IR11
  mov_int_to_movwt
  bpf_alu32_to_thumb_imm_comm
  bpf_alu32_to_thumb_imm_shift_comm
  bpf_alu32_to_thumb_imm
  nat_to_opcode_alu32
  nat_to_opcode_alu32_reg
  nat_to_opcode_alu32_imm
  jit_one
  jit_sequence (*
  jit_alu32_thumb_pc_add
  jit_alu32_thumb_pc *)
  jit_alu32_thumb_upd_store
  jit_alu32_thumb_store
  jit_alu32_thumb_upd_reset
  jit_alu32_thumb_reset1
  jit_alu32_thumb_reset
  jit_alu32_post
  jit_alu32_aux
  jit_list

  whole_compiler_aux
  whole_compiler
.

Open Scope string_scope.
    
Definition dxModuleTest := makeDXModuleWithUserIds 
  [ key_value2_def; jit_state_def]
  [ "key_value2";
    "arm_ofs"; "alu32_ofs";
    "jit_state";
    "input_len"; "input_ins"; "tp_kv"; "ld_set"; "st_set"; "tp_bin_len"; "tp_bin" ] SymbolIRs.

Close Scope string_scope.