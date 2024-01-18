From compcert Require Import Integers Memory Values.
From compcert.arm Require Import AsmSyntax BinSyntax.

From Coq Require Import Ascii String List ZArith.
Import ListNotations.

From bpf.comm Require Import ListAsArray.
From bpf.model Require Import Decode Encode PrintrBPF.
From bpf.jit.arm Require Import List32 JitState Arm32Decode ArmJITOpcode ArmJIT Arm32Decode PrintJIT.

Open Scope string_scope.

Definition test_sub_reg_int64: list int64 :=
[
(Int64.repr 0x00000000000010bc);
(Int64.repr 0x000000000000201c);
(Int64.repr 0x000000000000301c);
(Int64.repr 0x0000000000000095)
].

(**r arm32 instruction 

0000000000000000 sub_test:
; {
       0:	bc 10 00 00 00 00 00 00	w0 = w1
;     sum0 = x - y;
       1:	1c 20 00 00 00 00 00 00	w0 -= w2
;     sum = sum0 - z; /*
       2:	1c 30 00 00 00 00 00 00	w0 -= w3
;     return sum;
       3:	95 00 00 00 00 00 00 00	exit


*)

Compute print_rBPF_prog (decode_prog test_sub_reg_int64 (List.length test_sub_reg_int64)).

(**r print arm32 instruction

"0x0: r0 =.32 r1";
"0x1: r0 -=.32 r2";
"0x2: r0 <<=.32 0x1";
"0x3: r0 -=.32 r3";
"0x4: exit"
*)


Definition sub_reg_init_jitted_list := List32.create_int_list JITTED_LIST_MAX_LENGTH.

Definition sub_reg_init_jit_state: jit_state := {|
  pc_loc      := Int.zero;
  flag        := Vundef;
  regs_st     := Vundef;
  mrs_num     := 0;
  bpf_mrs     := [];
  ins_len     := List.length test_sub_reg_int64;
  ibpf        := test_sub_reg_int64; (*
  stack_len   := 0; *)
  stack_ofs   := 0;
  jitted_len  := 0;
  jitted_list := sub_reg_init_jitted_list;
  jit_mem     := Mem.empty;
|}.

Definition ibpf_len := (List.length (ibpf sub_reg_init_jit_state)).

Compute (jit_alu32_entry_points_list ibpf_len 0 false (ibpf sub_reg_init_jit_state) init_entry_point).

(**r entry_point

entry_len := 1;
entry_ps := [0%nat];

*)

Compute (jit_alu32 sub_reg_init_jit_state).

Definition final_jitted_state := 
  match jit_alu32 sub_reg_init_jit_state with
  | (Some st, _) => st
  | (None, _) => empty_jit_state
  end.

Compute final_jitted_state.

Definition ins_nth (n: nat) := List32.index (jitted_list final_jitted_state) (Int.repr (Z.of_nat n)).

Definition ins := ins_nth 1.

(*
Definition op := (decode_arm32 ins 21 4).
Compute op.
Compute int2Arm32DataProcessingRegOp op (decode_arm32 (ins_nth 1) 4 1).
Compute (arm32_decode (ins_nth 1)). *)

Definition epl := jit_alu32_entry_points_list (List.length (ibpf sub_reg_init_jit_state)) 0 false (ibpf sub_reg_init_jit_state) init_entry_point.

Definition entry_point := ListNat.index (entry_ps epl) 0.

Compute (arm32_decode_prog (jitted_list final_jitted_state) (jitted_len final_jitted_state)).

Definition ins64 (n: nat):= List64AsArray.index (ibpf final_jitted_state) (Int.repr (Z.of_nat n)).
Compute (jit_alu32_to_arm32_pass1 (List.length (ibpf final_jitted_state)) entry_point (ibpf final_jitted_state) init_jittedarm32).
Definition pre_jit :=
  match (jit_alu32_to_arm32_pass1 (List.length (ibpf final_jitted_state)) entry_point (ibpf final_jitted_state) init_jittedarm32) with
  | (Some res, _) => res
  | (None, _) => init_jittedarm32
  end.

Compute pre_jit.


(**r 
Add_R rd rn rm

Add_R R0 R0 R1

0000 000 0100 0 0000 0000 00000 00 0 0001 *)

Compute arm32_decode_prog (arm32 pre_jit) (arm32_len pre_jit).

(**r
need
- Load: R1, R2, R3
- Store: R0

*)

Compute print_jit_state final_jitted_state.

(**r 
     = {|
         ibpf_string :=
          ["0x0: r0 =.32 r1";
           "0x1: r0 -=.32 r2";
           "0x2: r0 -=.32 r3";
           "0x3: exit"];
         stack_size := 20;
         stack_nat := 0;
         jitted_len_nat := 21;
         jitted_string :=
          ["0x0: [sp + #0x0] := fp";
           "0x1: fp := r1";
           "0x2: [sp + #0x4] := r1";
           "0x3: [sp + #0x8] := r2";
           "0x4: [sp + #0xc] := r3";
           "0x5: [sp + #0x10] := ip";
           "0x6: r1 := [fp + #0x10]";
           "0x7: r2 := [fp + #0x18]";
           "0x8: r3 := [fp + #0x20]";
           "0x9: r0 := r1";
           "0xa: r0 := r0 - r2";
           "0xb: r0 := r0 - r3";
           "0xc: ip := #0x1";
           "0xd: [fp + #0x4] := ip";
           "0xe: [fp + #0x8] := r0";
           "0xf: ip := [sp + #0x10]";
           "0x10: r3 := [sp + #0xc]";
           "0x11: r2 := [sp + #0x8]";
           "0x12: r1 := [sp + #0x4]";
           "0x13: sp := [sp + #0x0]";
           "0x14: goto lr"]
       |}
     : jit_state_string


*)

(**r TODO: for a all_alu32 prog, can we do more optimization? *)