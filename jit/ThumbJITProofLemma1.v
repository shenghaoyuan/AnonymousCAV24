From compcert.common Require Import Values Memory AST.
From compcert.lib Require Import Integers.
From compcert.arm Require Import AsmSyntax ABinSem BinDecode.

From bpf.jit Require Import ThumbJITProofSubMem.

From Coq Require Import List ZArith Lia.
Open Scope nat_scope.
Open Scope bool_scope.
Open Scope asm.
Import ListNotations.

(**r referring to https://compcert.org/doc/html/compcert.backend.Asmgenproof0.html#exec_straight *)

Inductive exec_line:  list int -> aregset -> astack -> block -> mem ->
                      list int -> aregset -> astack -> block -> mem -> Prop :=
  | exec_line_one: forall jit_blk st_blk ofs i l ars0 ars1 astk0 astk1 astkb m0 m1 ins
    (Hfind: Mem.loadv Mint16unsigned m1 (Vptr jit_blk (Ptrofs.repr (Z.of_nat ofs))) = Some (Vint i) /\
            is_thumb2 i = false /\
            decode_thumb i = Some ins
            )
    (Hmem : Mem.unchanged_on (fun (b : block) (_ : Z) => b <> jit_blk /\ b <> st_blk /\ b <> astkb) m0 m1)
    (HMEM : sub_mem_blk l m1 jit_blk ofs)
    (HPC  : ars1#PC = aoffset_ptr ars0#PC isize)
    (HEXEC: aexec_instr false ins ars0 astk0 astkb m0 = ANext ars1 astk1 astkb m1),
      exec_line (i:: l) ars0 astk0 astkb m0
                l ars1 astk1 astkb m1

  | exec_line_two: forall jit_blk st_blk ofs i0 i1 l ars0 ars1 astk0 astk1 astkb m0 m1 ins
    (Hfind: Mem.loadv AST.Mint16unsigned m1 (Vptr jit_blk (Ptrofs.repr (Z.of_nat ofs))) = Some (Vint i0) /\
            is_thumb2 i0 = true /\
            Mem.loadv Mint16unsigned m1 (Val.add
              (Vptr jit_blk (Ptrofs.repr (Z.of_nat ofs))) (Vint (Int.repr 2))) = Some (Vint i1) /\
            decode_thumb2 i0 i1 = Some ins
            )
    (Hmem : Mem.unchanged_on (fun (b : block) (_ : Z) => b <> jit_blk /\ b <> st_blk /\ b <> astkb) m0 m1)
    (HMEM : sub_mem_blk l m1 jit_blk ofs)
    (HPC  : ars1#PC = aoffset_ptr ars0#PC wsize)
    (HEXEC: aexec_instr true ins ars0 astk0 astkb m0 = ANext ars1 astk1 astkb m1),
      exec_line (i0 :: i1 :: l) ars0 astk0 astkb m0
                l ars1 astk1 astkb m1

  | exec_line_step_one: forall jit_blk st_blk ofs i l0 l1 l2 ars0 ars1 ars2 astk0 astk1 astk2 astkb m0 m1 m2 ins
    (Hfind: Mem.loadv Mint16unsigned m1 (Vptr jit_blk (Ptrofs.repr (Z.of_nat ofs))) = Some (Vint i) /\
            is_thumb2 i = false /\
            decode_thumb i = Some ins
            )
    (Hmem : Mem.unchanged_on (fun (b : block) (_ : Z) => b <> jit_blk /\ b <> st_blk /\ b <> astkb) m0 m1)
    (HMEM : sub_mem_blk l0 m1 jit_blk ofs)
    (HPC  : ars1#PC = aoffset_ptr ars0#PC isize)

    (Hline: exec_line l1 ars1 astk1 astkb m1 l2 ars2 astk2 astkb m2),
      exec_line (i:: l1) ars0 astk0 astkb m0
                l2 ars2 astk2 astkb m2

  | exec_line_step_two: forall jit_blk st_blk ofs i0 i1 l0 l1 l2 ars0 ars1 ars2 astk0 astk1 astk2 astkb m0 m1 m2 ins
    (Hfind: Mem.loadv Mint16unsigned m1 (Vptr jit_blk (Ptrofs.repr (Z.of_nat ofs))) = Some (Vint i0) /\
            is_thumb2 i0 = true /\
            Mem.loadv Mint16unsigned m1 (Val.add
              (Vptr jit_blk (Ptrofs.repr (Z.of_nat ofs))) (Vint (Int.repr 2))) = Some (Vint i1) /\
            decode_thumb2 i0 i1 = Some ins
            )
    (Hmem : Mem.unchanged_on (fun (b : block) (_ : Z) => b <> jit_blk /\ b <> st_blk /\ b <> astkb) m0 m1)
    (HMEM : sub_mem_blk l0 m1 jit_blk ofs)
    (HPC  : ars1#PC = aoffset_ptr ars0#PC wsize)

    (Hline: exec_line l1 ars1 astk1 astkb m1 l2 ars2 astk2 astkb m2),
      exec_line (i0 :: i1 :: l1) ars0 astk0 astkb m0
                l2 ars2 astk2 astkb m2.