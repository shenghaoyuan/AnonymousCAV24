From compcert Require Import Integers Memdata Memory AST Values.
From compcert.arm Require Import AsmSyntax BinSyntax ABinSem.

From Coq Require Import Ascii String List ZArith.
Import ListNotations.

From bpf.comm Require Import ListAsArray.
From bpf.model Require Import Decode Encode PrintrBPF.
From bpf.jit.arm Require Import List32 JitState Arm32Decode ArmJITOpcode ArmJIT Arm32Decode PrintArm32 PrintJIT.

From bpf.example Require Import DebugExtraction.

Definition wrap_around_data_ascii:string :=  "AD3Awn4kb6FtcsyE0RU25U7f55Yncn3LP3oEx9Gl4qr7iDW7I8L6Pbw9jNnh0sE4DmCKuc" ++
"d1J8I34vn31W924y5GMS74vUrZQc08805aj4Tf66HgL1cO94os10V2s2GDQ825yNh9Yuq3" ++
"QHcA60xl31rdA7WskVtCXI7ruH1A4qaR6Uk454hm401lLmv2cGWt5KTJmr93d3JsGaRRPs" ++
"4HqYi4mFGowo8fWv48IcA3N89Z99nf0A0H2R6P0uI4Tir682Of3Rk78DUB2dIGQRRpdqVT" ++
"tLhgfET2gUGU65V3edSwADMqRttI9JPVz8JS37g5QZj4Ax56rU1u0m0K8YUs57UYG5645n" ++
"byNy4yqxu7".

Definition wrap_around_data_nat: list nat :=
  let ascii_list: list ascii := list_ascii_of_string wrap_around_data_ascii in
  map nat_of_ascii ascii_list.

Compute wrap_around_data_nat.

Definition wrap_around_data_byte: list memval :=
  let ascii_list: list ascii := list_ascii_of_string wrap_around_data_ascii in
  map (fun a => Byte (Byte.repr (Z.of_N (N_of_ascii a)))) ascii_list.

Compute wrap_around_data_byte.

Definition words:int := Int.repr 180. (**r (length data)/2 *)

(*
Fixpoint int64_to_listbyte (i:int64) (n:nat): list byte :=
  match n with
  | O => []
  | S n' => 
    let hd:byte := Byte.repr (Int64.unsigned i) in
    let res:int64 := Int64.shru i (Int64.repr 8) in
     hd::int64_to_listbyte res n'
  end.
*)

(** here we have lddw_high and lddw_low *)
Definition test_fletcher32_int64: list int64 :=
[
(Int64.repr 0x000000000000a0bc);
(Int64.repr 0x0000001000000a14);
(Int64.repr 0x0000000000000a63);
(Int64.repr 0x0000000000049a63);
(Int64.repr 0x0000000000086a63);
(Int64.repr 0x0000ffff000005b4);
(Int64.repr 0x00000000000053bc);
(Int64.repr 0x00000000001c0215);
(Int64.repr 0x00000167000202b5);
(Int64.repr 0x00000167000000b4);
(Int64.repr 0x0000000000010005);
(Int64.repr 0x00000000000020bc);
(Int64.repr 0x000000000000021c);
(Int64.repr 0x00000000000014bc);
(Int64.repr 0x00000000000041bc);
(Int64.repr 0x0000000200000104);
(Int64.repr 0x0000000000004469);
(Int64.repr 0x000000000000450c);
(Int64.repr 0x000000000000530c);
(Int64.repr 0xffffffff00000004);
(Int64.repr 0x00000000fff80055);
(Int64.repr 0x00000000000054bc);
(Int64.repr 0x0000ffff00000454);
(Int64.repr 0x00000010000006b4);
(Int64.repr 0x00000000000050bc);
(Int64.repr 0x000000000000607c);
(Int64.repr 0x00000000000045bc);
(Int64.repr 0x000000000000050c);
(Int64.repr 0x00000000000034bc);
(Int64.repr 0x0000ffff00000454);
(Int64.repr 0x00000010000006b4);
(Int64.repr 0x00000000000030bc);
(Int64.repr 0x000000000000607c);
(Int64.repr 0x00000000000043bc);
(Int64.repr 0x000000000000030c);
(Int64.repr 0x00000000ffe30005);
(Int64.repr 0x00000000000051bc);
(Int64.repr 0x0000ffff00000154);
(Int64.repr 0x00000010000004b4);
(Int64.repr 0x000000000000457c);
(Int64.repr 0x000000000000510c);
(Int64.repr 0x00000000000030bc);
(Int64.repr 0x0000ffff00000054);
(Int64.repr 0x00000010000002b4);
(Int64.repr 0x000000000000237c);
(Int64.repr 0x000000000000300c);
(Int64.repr 0x00000010000004b4);
(Int64.repr 0x000000000000406c);
(Int64.repr 0x000000000000104c);
(Int64.repr 0x000000000008a661);
(Int64.repr 0x000000000004a961);
(Int64.repr 0x0000001000000a04);
(Int64.repr 0x0000000000000095)
].

(*
Open Scope string_scope.

Compute print_rBPF_prog (decode_prog test_fletcher32_int64 (List.length test_fletcher32_int64)).

= ["0x0: r0 =.32 r10";
   "0x1: r10 -=.32 0x10";
   "0x2: *(u32 *)(r10 + 0x0) = r0";
   "0x3: *(u32 *)(r10 + 0x4) = r9";
   "0x4: *(u32 *)(r10 + 0x8) = r6";
   "0x5: r5 =.32 0xffff";
   "0x6: r3 =.32 r5";
   "0x7: if r2 == 0x0 goto 0x1c";
   "0x8: if r2 <= 0x167 goto 0x2";
   "0x9: r0 =.32 0x167";
   "0xa: goto 0x1";
   "0xb: r0 =.32 r2";
   "0xc: r2 -=.32 r0";
   "0xd: r4 =.32 r1";
   "0xe: r1 =.32 r4";
   "0xf: r1 +=.32 0x2";
   "0x10: r4 = *(u16 *)(r4 + 0x0)";
   "0x11: r5 +=.32 r4";
   "0x12: r3 +=.32 r5";
   "0x13: r0 +=.32 -0x1";
   "0x14: if r0 != 0x0 goto -0x8";
   "0x15: r4 =.32 r5";
   "0x16: r4 &=.32 0xffff";
   "0x17: r6 =.32 0x10";
   "0x18: r0 =.32 r5";
   "0x19: r0 >>=.32 r6";
   "0x1a: r5 =.32 r4";
   "0x1b: r5 +=.32 r0";
   "0x1c: r4 =.32 r3";
   "0x1d: r4 &=.32 0xffff";
   "0x1e: r6 =.32 0x10";
   "0x1f: r0 =.32 r3";
   "0x20: r0 >>=.32 r6";
   "0x21: r3 =.32 r4";
   "0x22: r3 +=.32 r0";
   "0x23: goto -0x1d";
   "0x24: r1 =.32 r5";
   "0x25: r1 &=.32 0xffff";
   "0x26: r4 =.32 0x10";
   "0x27: r5 >>=.32 r4";
   "0x28: r1 +=.32 r5";
   "0x29: r0 =.32 r3";
   "0x2a: r0 &=.32 0xffff";
   "0x2b: r2 =.32 0x10";
   "0x2c: r3 >>=.32 r2";
   "0x2d: r0 +=.32 r3";
   "0x2e: r4 =.32 0x10";
   "0x2f: r0 <<=.32 r4";
   "0x30: r0 |=.32 r1";
   "0x31: r6 = *(u32 *)(r10 + 0x8)";
   "0x32: r9 = *(u32 *)(r10 + 0x4)";
   "0x33: r10 +=.32 0x10";
   "0x34: exit"]
 : list string

where,
- epl = [0; 5; 36; 11; 9; 12; 17; 13; 21; 51]
*)


Definition fletcher32_init_jitted_list := List32.create_int_list JITTED_LIST_MAX_LENGTH.

Definition fletcher32_init_jit_state: jit_state := {|
  pc_loc      := Int.zero;
  flag        := Vundef;
  regs_st     := Vundef;
  mrs_num     := 0;
  bpf_mrs     := [];
  ins_len     := List.length test_fletcher32_int64;
  ibpf        := test_fletcher32_int64; (*
  stack_len   := 0; *)
  stack_ofs   := 0;
  jitted_len  := 0;
  jitted_list := fletcher32_init_jitted_list;
  jit_mem     := Mem.empty;
|}.

Definition ibpf_len := (List.length (ibpf fletcher32_init_jit_state)).

Compute (jit_alu32_entry_points_list ibpf_len 0 false (ibpf fletcher32_init_jit_state) init_entry_point).

(**r epl = [0; 5; 36; 11; 9; 12; 17; 13; 21; 51] *)
Definition jittedarm :=
  match fst (jit_alu32_to_arm32_pass1 ibpf_len 0 (ibpf fletcher32_init_jit_state) init_jittedarm32) with
  | Some st => st
  | None => init_jittedarm32
  end.

(**r
    entry_point = 0
  - "0x0: r0 =.32 r10";
    "0x1: r10 -=.32 0x10"

    entry_point = 5
  - "0x5: r5 =.32 0xffff";
    "0x6: r3 =.32 r5";

    entry_point = 36
  - "0x24: r1 =.32 r5";
    "0x25: r1 &=.32 0xffff";
    "0x26: r4 =.32 0x10";
    "0x27: r5 >>=.32 r4";
    "0x28: r1 +=.32 r5";
    "0x29: r0 =.32 r3";
    "0x2a: r0 &=.32 0xffff";
    "0x2b: r2 =.32 0x10";
    "0x2c: r3 >>=.32 r2";
    "0x2d: r0 +=.32 r3";
    "0x2e: r4 =.32 0x10";
    "0x2f: r0 <<=.32 r4";
    "0x30: r0 |=.32 r1";

    entry_point = 11
  - "0xb: r0 =.32 r2";
    "0xc: r2 -=.32 r0";
    "0xd: r4 =.32 r1";
    "0xe: r1 =.32 r4";
    "0xf: r1 +=.32 0x2";

    entry_point = 9
  - "0x9: r0 =.32 0x167";

    entry_point = 12
  - "0xc: r2 -=.32 r0";
    "0xd: r4 =.32 r1";
    "0xe: r1 =.32 r4";
    "0xf: r1 +=.32 0x2";

    entry_point = 17
  - "0x11: r5 +=.32 r4";
    "0x12: r3 +=.32 r5";
    "0x13: r0 +=.32 -0x1";

    entry_point = 13
  - "0xd: r4 =.32 r1";
    "0xe: r1 =.32 r4";
    "0xf: r1 +=.32 0x2";

    entry_point = 21
  - "0x15: r4 =.32 r5";
    "0x16: r4 &=.32 0xffff";
    "0x17: r6 =.32 0x10";
    "0x18: r0 =.32 r5";
    "0x19: r0 >>=.32 r6";
    "0x1a: r5 =.32 r4";
    "0x1b: r5 +=.32 r0";
    "0x1c: r4 =.32 r3";
    "0x1d: r4 &=.32 0xffff";
    "0x1e: r6 =.32 0x10";
    "0x1f: r0 =.32 r3";
    "0x20: r0 >>=.32 r6";
    "0x21: r3 =.32 r4";
    "0x22: r3 +=.32 r0";

    entry_point = 51
  - "0x33: r10 +=.32 0x10";
  *)
Compute jittedarm.
Definition arm32_syntax := print_arm32_prog (arm32_decode_prog (arm32 jittedarm) (arm32_len jittedarm)).
Compute arm32_syntax.

Compute (jit_alu32 fletcher32_init_jit_state).
Definition fletcher32_main :=
  let final_state := jit_alu32 fletcher32_init_jit_state in
  match fst final_state with
  | Some st => print_arm32_prog (arm32_decode_prog (jitted_list st) (jitted_len st))
  | None => []
  end.

(*
Compute fletcher32_main.

     = ["0x0: ip := r1"%string;
       "0x1: [sp + #0x4] := r10"%string;
       "0x2: r10 := [ip + #0x58]"%string;
       "0x3: r0 := r10"%string;
       "0x4: r10 := r10 - #0x10"%string;
       "0x5: [ip + #0x8] := r0"%string;
       "0x6: [ip + #0x58] := r10"%string;
       "0x7: r10 := [sp + #0x4]"%string;
       "0x8: sp := [sp + #0x0]"%string;
       "0x9: goto lr"%string;
       "0xa: ip := r1"%string;
       "0xb: [sp + #0x4] := r3"%string;
       "0xc: [sp + #0x8] := r5"%string;
       "0xd: [sp + #0xc] := fp"%string;
       "0xe: fp := #0xffff"%string;
       "0xf: fp := (#0x0) << 16"%string;
       "0x10: r5 := fp"%string;
       "0x11: r3 := r5"%string;
       "0x12: [ip + #0x20] := r3"%string;
       "0x13: [ip + #0x30] := r5"%string;
       "0x14: fp := [sp + #0xc]"%string;
       "0x15: r5 := [sp + #0x8]"%string;
       "0x16: r3 := [sp + #0x4]"%string;
       "0x17: sp := [sp + #0x0]"%string;
       "0x18: goto lr"%string;
       "0x19: ip := r1"%string;
       "0x1a: [sp + #0x4] := r1"%string;
       "0x1b: [sp + #0x8] := r2"%string;
       "0x1c: [sp + #0xc] := r3"%string;
       "0x1d: [sp + #0x10] := r4"%string;
       "0x1e: [sp + #0x14] := r5"%string;
       "0x1f: [sp + #0x18] := fp"%string;
       "0x20: r3 := [ip + #0x20]"%string;
       "0x21: r5 := [ip + #0x30]"%string;
       "0x22: r1 := r5"%string;
       "0x23: fp := #0xffff"%string;
       "0x24: fp := (#0x0) << 16"%string;
       "0x25: r1 := r1 & fp"%string;
       "0x26: r4 := #0x10"%string;
       "0x27: cmp r4 and #0x20 => update flags"%string;
       "0x28: goto 0x4"%string;
       "0x29: fp := #0xb"%string;
       "0x2a: [ip + #0x4] := fp"%string;
       "0x2b: goto 0x0"%string;
       "0x2c: r5 := r5 >> r4"%string;
       "0x2d: r1 := r1 + r5"%string;
       "0x2e: r0 := r3"%string;
       "0x2f: fp := #0xffff"%string;
       "0x30: fp := (#0x0) << 16"%string;
       "0x31: r0 := r0 & fp"%string;
       "0x32: r2 := #0x10"%string;
       "0x33: cmp r2 and #0x20 => update flags"%string;
       "0x34: goto 0x4"%string;
       "0x35: fp := #0xb"%string;
       "0x36: [ip + #0x4] := fp"%string;
       "0x37: goto 0x0"%string;
       "0x38: r3 := r3 >> r2"%string;
       "0x39: r0 := r0 + r3"%string;
       "0x3a: r4 := #0x10"%string;
       "0x3b: cmp r4 and #0x20 => update flags"%string;
       "0x3c: goto 0x4"%string;
       "0x3d: fp := #0xb"%string;
       "0x3e: [ip + #0x4] := fp"%string;
       "0x3f: goto 0x0"%string;
       "0x40: r0 := r0 << r4"%string;
       "0x41: r0 := r0 | r1"%string;
       "0x42: [ip + #0x8] := r0"%string;
       "0x43: [ip + #0x10] := r1"%string;
       "0x44: [ip + #0x18] := r2"%string;
       "0x45: [ip + #0x20] := r3"%string;
       "0x46: [ip + #0x28] := r4"%string;
       "0x47: [ip + #0x30] := r5"%string;
       "0x48: fp := [sp + #0x18]"%string;
       "0x49: r5 := [sp + #0x14]"%string;
       "0x4a: r4 := [sp + #0x10]"%string;
       "0x4b: r3 := [sp + #0xc]"%string;
       "0x4c: r2 := [sp + #0x8]"%string;
       "0x4d: r1 := [sp + #0x4]"%string;
       "0x4e: sp := [sp + #0x0]"%string;
       "0x4f: goto lr"%string;
       "0x50: ip := r1"%string;
       "0x51: [sp + #0x4] := r1"%string;
       "0x52: [sp + #0x8] := r2"%string;
       "0x53: [sp + #0xc] := r4"%string;
       "0x54: r1 := [ip + #0x10]"%string;
       "0x55: r2 := [ip + #0x18]"%string;
       "0x56: r0 := r2"%string;
       "0x57: r2 := r2 - r0"%string;
       "0x58: r4 := r1"%string;
       "0x59: r1 := r4"%string;
       "0x5a: r1 := r1 + #0x2"%string;
       "0x5b: [ip + #0x8] := r0"%string;
       "0x5c: [ip + #0x10] := r1"%string;
       "0x5d: [ip + #0x18] := r2"%string;
       "0x5e: [ip + #0x28] := r4"%string;
       "0x5f: r4 := [sp + #0xc]"%string;
       "0x60: r2 := [sp + #0x8]"%string;
       "0x61: r1 := [sp + #0x4]"%string;
       "0x62: sp := [sp + #0x0]"%string;
       "0x63: goto lr"%string;
       "0x64: ip := r1"%string;
       "0x65: [sp + #0x4] := fp"%string;
       "0x66: fp := #0x167"%string;
       "0x67: fp := (#0x0) << 16"%string;
       "0x68: r0 := fp"%string;
       "0x69: [ip + #0x8] := r0"%string;
       "0x6a: fp := [sp + #0x4]"%string;
       "0x6b: sp := [sp + #0x0]"%string;
       "0x6c: goto lr"%string;
       "0x6d: ip := r1"%string;
       "0x6e: [sp + #0x4] := r1"%string;
       "0x6f: [sp + #0x8] := r2"%string;
       "0x70: [sp + #0xc] := r4"%string;
       "0x71: r0 := [ip + #0x8]"%string;
       "0x72: r1 := [ip + #0x10]"%string;
       "0x73: r2 := r2 - r0"%string;
       "0x74: r4 := r1"%string;
       "0x75: r1 := r4"%string;
       "0x76: r1 := r1 + #0x2"%string;
       "0x77: [ip + #0x10] := r1"%string;
       "0x78: [ip + #0x18] := r2"%string;
       "0x79: [ip + #0x28] := r4"%string;
       "0x7a: r4 := [sp + #0xc]"%string;
       "0x7b: r2 := [sp + #0x8]"%string;
       "0x7c: r1 := [sp + #0x4]"%string;
       "0x7d: sp := [sp + #0x0]"%string;
       "0x7e: goto lr"%string;
       "0x7f: ip := r1"%string;
       "0x80: [sp + #0x4] := r3"%string;
       "0x81: [sp + #0x8] := r4"%string;
       "0x82: [sp + #0xc] := r5"%string;
       "0x83: [sp + #0x10] := fp"%string;
       "0x84: r4 := [ip + #0x28]"%string;
       "0x85: r5 := r5 + r4"%string;
       "0x86: r3 := r3 + r5"%string;
       "0x87: fp := #0xffff"%string;
       "0x88: fp := (#0xffff) << 16"%string;
       "0x89: r0 := r0 + fp"%string;
       "0x8a: [ip + #0x8] := r0"%string;
       "0x8b: [ip + #0x20] := r3"%string;
       "0x8c: [ip + #0x30] := r5"%string;
       "0x8d: fp := [sp + #0x10]"%string;
       "0x8e: r5 := [sp + #0xc]"%string;
       "0x8f: r4 := [sp + #0x8]"%string;
       "0x90: r3 := [sp + #0x4]"%string;
       "0x91: sp := [sp + #0x0]"%string;
       "0x92: goto lr"%string;
       "0x93: ip := r1"%string;
       "0x94: [sp + #0x4] := r1"%string;
       "0x95: [sp + #0x8] := r4"%string;
       "0x96: r1 := [ip + #0x10]"%string;
       "0x97: r4 := r1"%string;
       "0x98: r1 := r4"%string;
       "0x99: r1 := r1 + #0x2"%string;
       "0x9a: [ip + #0x10] := r1"%string;
       "0x9b: [ip + #0x28] := r4"%string;
       "0x9c: r4 := [sp + #0x8]"%string;
       "0x9d: r1 := [sp + #0x4]"%string;
       "0x9e: sp := [sp + #0x0]"%string;
       "0x9f: goto lr"%string;
       "0xa0: ip := r1"%string;
       "0xa1: [sp + #0x4] := r3"%string;
       "0xa2: [sp + #0x8] := r4"%string;
       "0xa3: [sp + #0xc] := r5"%string;
       "0xa4: [sp + #0x10] := r6"%string;
       "0xa5: [sp + #0x14] := fp"%string;
       "0xa6: r3 := [ip + #0x20]"%string;
       "0xa7: r5 := [ip + #0x30]"%string;
       "0xa8: r4 := r5"%string;
       "0xa9: fp := #0xffff"%string;
       "0xaa: fp := (#0x0) << 16"%string;
       "0xab: r4 := r4 & fp"%string;
       "0xac: r6 := #0x10"%string;
       "0xad: r0 := r5"%string;
       "0xae: cmp r6 and #0x20 => update flags"%string;
       "0xaf: goto 0x4"%string;
       "0xb0: fp := #0xb"%string;
       "0xb1: [ip + #0x4] := fp"%string;
       "0xb2: goto 0x0"%string;
       "0xb3: r0 := r0 >> r6"%string;
       "0xb4: r5 := r4"%string;
       "0xb5: r5 := r5 + r0"%string;
       "0xb6: r4 := r3"%string;
       "0xb7: fp := #0xffff"%string;
       "0xb8: fp := (#0x0) << 16"%string;
       "0xb9: r4 := r4 & fp"%string;
       "0xba: r6 := #0x10"%string;
       "0xbb: r0 := r3"%string;
       "0xbc: cmp r6 and #0x20 => update flags"%string;
       "0xbd: goto 0x4"%string;
       "0xbe: fp := #0xb"%string;
       "0xbf: [ip + #0x4] := fp"%string;
       "0xc0: goto 0x0"%string;
       "0xc1: r0 := r0 >> r6"%string;
       "0xc2: r3 := r4"%string;
       "0xc3: r3 := r3 + r0"%string;
       "0xc4: [ip + #0x8] := r0"%string;
       "0xc5: [ip + #0x20] := r3"%string;
       "0xc6: [ip + #0x28] := r4"%string;
       "0xc7: [ip + #0x30] := r5"%string;
       "0xc8: [ip + #0x38] := r6"%string;
       "0xc9: fp := [sp + #0x14]"%string;
       "0xca: r6 := [sp + #0x10]"%string;
       "0xcb: r5 := [sp + #0xc]"%string;
       "0xcc: r4 := [sp + #0x8]"%string;
       "0xcd: r3 := [sp + #0x4]"%string;
       "0xce: sp := [sp + #0x0]"%string;
       "0xcf: goto lr"%string;
       "0xd0: ip := r1"%string;
       "0xd1: [sp + #0x4] := r10"%string;
       "0xd2: r10 := r10 + #0x10"%string;
       "0xd3: [ip + #0x58] := r10"%string;
       "0xd4: r10 := [sp + #0x4]"%string;
       "0xd5: sp := [sp + #0x0]"%string;
       "0xd6: goto lr"%string]
     : list string


*)
(*
Extraction "/home/shyuan/GitLab/workspace/jit/example/fletcher32_main1.ml" fletcher32_main. *)
