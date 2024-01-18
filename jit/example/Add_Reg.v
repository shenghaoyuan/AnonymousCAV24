From compcert Require Import Integers Memdata Memory AST Values.
From compcert.arm Require Import AsmSyntax BinSyntax ABinSem.

From Coq Require Import Ascii String List ZArith.
Import ListNotations.

From bpf.comm Require Import ListAsArray.
From bpf.model Require Import Decode Encode PrintrBPF.
From bpf.jit.arm Require Import List32 JitState Arm32Decode ArmJITOpcode ArmJIT Arm32Decode PrintJIT.

From bpf.example Require Import DebugExtraction.

Open Scope string_scope.

Definition test_add_reg_int64: list int64 :=
[
(Int64.repr 0x00000000000020bc);
(Int64.repr 0x000000000000100c);
(Int64.repr 0x000000000000300c);
(Int64.repr 0x0000000000000095)
].

(**r arm32 instruction 

0000000000000000 fletcher32:
; {
       0:	bc 20 00 00 00 00 00 00	w0 = w2
;     sum0 = x + y;
       1:	0c 10 00 00 00 00 00 00	w0 += w1
;     sum = sum0 + z; /*
       2:	0c 30 00 00 00 00 00 00	w0 += w3
;     return sum;
       3:	95 00 00 00 00 00 00 00	exit

*)

Compute print_rBPF_prog (decode_prog test_add_reg_int64 (List.length test_add_reg_int64)).

(**r print arm32 instruction

"0x0: r0 =.32 r2";
"0x1: r0 +=.32 r1";
"0x2: r0 +=.32 r3";
"0x3: exit"
*)


Definition add_reg_init_jitted_list := List32.create_int_list JITTED_LIST_MAX_LENGTH.

Definition add_reg_init_jit_state: jit_state := {|
  pc_loc      := Int.zero;
  flag        := Vundef;
  regs_st     := Vundef;
  mrs_num     := 0;
  bpf_mrs     := [];
  ins_len     := List.length test_add_reg_int64;
  ibpf        := test_add_reg_int64; (*
  stack_len   := 0; *)
  stack_ofs   := 0;
  jitted_len  := 0;
  jitted_list := add_reg_init_jitted_list;
  jit_mem     := Mem.empty;
|}.

Definition ibpf_len := (List.length (ibpf add_reg_init_jit_state)).

Compute (jit_alu32_entry_points_list ibpf_len 0 false (ibpf add_reg_init_jit_state) init_entry_point).

(**r entry_point

entry_len := 1;
entry_ps := [0%nat];

*)

Compute (jit_alu32 add_reg_init_jit_state).

Definition final_jitted_state := 
  match jit_alu32 add_reg_init_jit_state with
  | (Some st, _) => st
  | (None, _) => empty_jit_state
  end.
(*
Compute final_jitted_state. *)

Definition ins_nth (n: nat) := List32.index (jitted_list final_jitted_state) (Int.repr (Z.of_nat n)).

Definition ins := ins_nth 1.

(*
Compute int2arm32_op1 (decode_arm32 ins 25 3). *)
(*
Definition op := (decode_arm32 ins 21 4).
Compute op.
Compute int2Arm32DataProcessingRegOp op (decode_arm32 (ins_nth 1) 4 1).
Compute (arm32_decode (ins_nth 1)). *)

Definition epl := jit_alu32_entry_points_list (List.length (ibpf add_reg_init_jit_state)) 0 false (ibpf add_reg_init_jit_state) init_entry_point.

Definition entry_point := ListNat.index (entry_ps epl) 0.

Compute (arm32_decode_prog (jitted_list final_jitted_state) (jitted_len final_jitted_state)).

Definition ins64 (n: nat):= List64AsArray.index (ibpf final_jitted_state) (Int.repr (Z.of_nat n)).

Definition core_ins := jit_alu32_to_arm32_pass1 (List.length (ibpf final_jitted_state)) entry_point (ibpf final_jitted_state) init_jittedarm32.

Definition pre_jit :=
  match core_ins with
  | (Some res, _) => res
  | (None, _) => init_jittedarm32
  end.

Compute pre_jit.
(*
Compute (int2Arm32DataProcessingRegOp (decode_arm32 (Int.repr 8388609) 21 4) (decode_arm32 (Int.repr 8388609) 4 1) ).
*)
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

Compute (jitted_list final_jitted_state).

Compute BinDecode.decode (Int.repr 93167616).

(**r 010 1100 0 1101 1010 000000000000 *)

Compute arm32_decode_prog (jitted_list final_jitted_state) (jitted_len final_jitted_state).

Compute print_jit_state final_jitted_state.

(**r
     = {|
         ibpf_string :=
           ["0x0: r0 =.32 r2";
           "0x1: r0 +=.32 r1";
           "0x2: r0 +=.32 r3"; "0x3: exit"];
         stack_size := 20;
         stack_nat := 0;
         jitted_len_nat := 21;
         jitted_string :=
          ["0x0: ip := r1";
           "0x1: [sp + #0x4] := r1";
           "0x2: [sp + #0x8] := r2";
           "0x3: [sp + #0xc] := r3";
           "0x4: [sp + #0x10] := fp";
           "0x5: r1 := [ip + #0x10]";
           "0x6: r2 := [ip + #0x18]";
           "0x7: r3 := [ip + #0x20]";
           "0x8: r0 := r2";
           "0x9: r0 := r0 + r1";
           "0xa: r0 := r0 + r3";
           "0xb: fp := #0x1";
           "0xc: [ip + #0x4] := fp";
           "0xd: [ip + #0x8] := r0";
           "0xe: fp := [sp + #0x10]";
           "0xf: r3 := [sp + #0xc]";
           "0x10: r2 := [sp + #0x8]";
           "0x11: r1 := [sp + #0x4]";
           "0x12: ip := [sp + #0x0]";
           "0x13: sp := ip"; "0x14: goto lr"]
       |}
     : jit_state_string
*)
Compute final_jitted_state.
(**r TODO: for a all_alu32 prog, can we do more optimization? *)

Definition init_mem := Mem.alloc Mem.empty 0 88.

(**r
Definition init_jit_state := {|
  pc := 0;
  flag := 0;
  R0 := 0LLU;
  R1 := 1LLU;
  R2 := 2LLU;
  R3 := 3LLU;
  R4 := 0LLU;
  ...
  R9 := 0LLU;
|}.
*)

Definition jit_state_memval_list : list memval :=
[ Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; (**r pc := 0 *)

  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; (**r flag := 0 *)

  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero;
  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; (**r R0 := 0 *)

  Byte Byte.one;  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero;
  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero;  (**r R1 := 1 *)

  Byte (Byte.repr 2); Byte Byte.zero; Byte Byte.zero; Byte Byte.zero;
  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; (**r R2 := 2 *)

  Byte (Byte.repr 3); Byte Byte.zero; Byte Byte.zero; Byte Byte.zero;
  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; (**r R3 := 3 *)

  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero;
  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; (**r R4 := 0 *)

  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero;
  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; (**r R5 := 0 *)

  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero;
  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero;  (**r R6 := 0 *)

  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero;
  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero;  (**r R7 := 0 *)

  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero;
  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero;  (**r R8 := 0 *)

  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero;
  Byte Byte.zero; Byte Byte.zero; Byte Byte.zero; Byte Byte.zero   (**r R9 := 0 *)
].

Definition jit_state_blk: block := (snd init_mem).

(**r mem1 includes the jit_state *)
Definition mem1 :=
  match Mem.storebytes (fst init_mem) jit_state_blk 0%Z jit_state_memval_list with
  | Some m => m
  | None => Mem.empty
  end.

(**r Now we store jitted arm32 to a new block *)

Fixpoint calc_jitted_code_aux (fuel pc: nat) (l: list int): list int :=
  match fuel with
  | O => []
  | S n =>
    let ins := List32.index l (Int.repr (Z.of_nat pc)) in
      ins :: calc_jitted_code_aux n (S pc) l
  end.

Definition calc_jitted_code (len: nat) (l: list int): list int :=
  calc_jitted_code_aux len 0 l.

Compute calc_jitted_code 
(jitted_len final_jitted_state) (jitted_list final_jitted_state).

Definition int2listmemval (i: int): list memval := encode_val Mint32 (Vint i).

Definition jitted_arm_memval_list: list memval :=
  let l := map int2listmemval (calc_jitted_code (jitted_len final_jitted_state) (jitted_list final_jitted_state)) in
    flat_map (fun x => x) l.

Compute jitted_arm_memval_list.

(**r mem2 includes the jit_state and the jitted_arm_code *)

Definition init_mem2 := Mem.alloc mem1 0 (Z.of_nat (List.length jitted_arm_memval_list)).
Definition jitted_arm_blk := snd init_mem2.

Definition mem2 :=
  match Mem.storebytes (fst init_mem2) jitted_arm_blk 0%Z jitted_arm_memval_list with
  | Some m => m
  | None => Mem.empty
  end.

(**r input: jitted_start_addr -> jit_state_start_addr -> result *)
Definition test_signature :=
  {| sig_args := [Tint; Tint]; sig_res := Tint; sig_cc := cc_default |}.


(**r bin_exec
     : nat -> signature -> Z -> ptrofs -> list val -> mem -> option (val * mem)

fuel -> test_signature -> stack_size -> Ptrofs.zero -> [Vptr jit_state_blk Ptrofs.zero;  Vptr jitted_arm_blk Ptrofs.zero] -> mem2  *)

Definition fuel: nat := 1000.

Definition test_list_val: list val := [Vptr jitted_arm_blk Ptrofs.zero;  Vptr jit_state_blk Ptrofs.zero].

Definition print_registers (m: Mem.mem) (b: block) (len: nat): list memval :=
  match Mem.loadbytes m b 0 (Z.of_nat len) with
  | Some l => l
  | None => []
  end
.

Definition test_compcertbin :=
  match bin_exec fuel test_signature 56%Z Ptrofs.zero test_list_val mem2 with
  | Some res => print_registers (snd res) jit_state_blk (List.length jit_state_memval_list)
  | None => []
  end.


(**r remark: ExtrOCamlInt63 will override the extraction of comparison to int *)
(*
Extraction "/home/shyuan/GitLab/workspace/jit/example/test_compcertbin1.ml" test_compcertbin. *)


(**r
Definition final_jit_state := {|
  pc := 0;
  flag := 1;
  R0 := 6LLU;
  R1 := 1LLU;
  R2 := 2LLU;
  R3 := 3LLU;
  R4 := 0LLU;
  ...
  R9 := 0LLU;
|}.

*)
