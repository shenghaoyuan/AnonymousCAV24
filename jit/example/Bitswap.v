From compcert Require Import Integers Memdata Memory AST Values.
From compcert.arm Require Import AsmSyntax BinSyntax ABinSem BinDecode.

From Coq Require Import Ascii String List ZArith.
Import ListNotations.

From bpf.comm Require Import ListAsArray Regs MemRegion rBPFMonadOp.
From bpf.rbpf32 Require Import TSDecode Analyzer.
From bpf.jit Require Import WholeCompiler PrintThumb PrintJIT.

From bpf.jit.example Require Import DebugExtraction.

Definition test_bitswap_int64: list int64 :=
[
(Int64.repr 0x0000000000011371);
(Int64.repr 0x00000001000002b4);
(Int64.repr 0x00000001000004b4);
(Int64.repr 0x000000000000346c);
(Int64.repr 0x0000000000021571);
(Int64.repr 0x000000000000526c);
(Int64.repr 0x00000000000026bc);
(Int64.repr 0x000000000000464c);
(Int64.repr 0xffffffff000006a4);
(Int64.repr 0x0000000000001171);
(Int64.repr 0x00000000000010bc);
(Int64.repr 0x000000000000605c);
(Int64.repr 0x000000000000145c);
(Int64.repr 0x000000000000347c);
(Int64.repr 0x000000000000546c);
(Int64.repr 0x000000000000404c);
(Int64.repr 0x000000000000125c);
(Int64.repr 0x000000000000527c);
(Int64.repr 0x000000000000326c);
(Int64.repr 0x000000000000204c);
(Int64.repr 0x000000ff00000054);
(Int64.repr 0x0000000000000095)
].
Compute (analyzer test_bitswap_int64).
Definition bitswap_ibpf_main := whole_compiler test_bitswap_int64.
(*
Extraction "/home/shyuan/GitLab/certrbpf-jit/jit/example/bitswap_main.ml" bitswap_ibpf_main. *)
