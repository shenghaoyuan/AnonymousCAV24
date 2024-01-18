From compcert.lib Require Import Integers Coqlib Maps.
From compcert.common Require Import AST Values Events Globalenvs Memory Memtype.
From compcert.cfrontend Require Import Ctypes.
From compcert.backend Require Import Locations.
From compcert.arm Require Import AsmSyntax ABinSem.
From Coq Require Import ZArith Lia List.

From bpf.comm Require Import JITCall.
From bpf.jit Require Import ThumbJIT WholeCompiler.
From bpf.rbpf32 Require Import TSSyntax JITConfig TSDecode.

Open Scope Z_scope.
Import ListNotations.


(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain (but do not enforce)
  the convention that integer registers are mapped to values of
  type [Tint], float registers to values of type [Tfloat],
  and condition bits to either [Vzero] or [Vone]. *)

(** Conventional names for stack pointer ([SP]) *)

Definition exec_bin_code (bl: bin_code) (ofs: nat) (jit_blk: block)
  (rs: regset) (m: mem): outcome :=
  let (m1, st_blk) := Mem.alloc m 0 state_block_size in
    match copy_to rs st_blk m1 with
    | None => Stuck
    | Some m2 =>
      match init_state compcertbin_signature stack_block_size Ptrofs.zero
            [ Val.add (Vptr jit_blk Ptrofs.zero)
                      (Vint (Int.repr (Z.of_nat (Nat.mul 4 ofs))));
              (Vptr st_blk Ptrofs.zero)] m2 with
      | AStuck => Stuck
      | ANext ars1 stk1 stkb1 am =>
        match exec_bin_list bl ars1 stk1 stkb1 am with
        | AStuck => Stuck
        | ANext ars2 stk2 stkb2 am2 =>
          if is_final_state ars2 then
            if get_result_bool AST.Tint (ars2 IR0) then
              match copy_from rs st_blk am2 with
              | None => Stuck
              | Some rs1 => Next rs1 m
              end
            else Stuck
          else Stuck
        end
      end
    end.

Section RELSEM_B.

Hypothesis _bpf_get_call: ident -> genv -> option fundef.
Hypothesis memory_region_map: mem -> permission -> memory_chunk -> val -> block -> ptrofs -> Prop.

(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual eBPF instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the eBPF reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above. *)

(** Execution of the instruction at [rs PC]. *)

Inductive bstep (c: code) (bl: list (nat *(nat * bin_code))) (jit_blk: block) (ge: genv):
    state -> trace -> state -> Prop :=
  | bexec_step_alu32:
      forall v n ofs rs m rs' m' l o r ri,
      rs#BPC = Vint (Int.repr (Z.of_nat v)) ->
      find_instr v c = Some (Palu32 o r ri) ->
      List.nth_error bl n = Some (v, (ofs, l)) ->
      code_subset_in_blk l ofs jit_blk m = true ->
      (**r big-step *)
      exec_bin_code l ofs jit_blk rs m = Next rs' m' ->
      bstep c bl jit_blk ge (State rs m) E0 (State rs' m')

  | bexec_step_jmp_always:
      forall v l rs m rs' m',
      rs#BPC = Vint (Int.repr (Z.of_nat v)) ->
      find_instr v c = Some (Pjmp l) ->
      goto_label c l rs m = Next rs' m' ->
      bstep c bl jit_blk ge (State rs m) E0 (State rs' m')

  | bexec_step_jmp_cond:
      forall v o r ri l rs m rs' m',
      rs#BPC = Vint (Int.repr (Z.of_nat v)) ->
      find_instr v c = Some (Pjmpcmp o r ri l) ->
      exec_branch c l rs m (eval_cmp o rs m r ri) = Next rs' m' ->
      bstep c bl jit_blk ge (State rs m) E0 (State rs' m')

  | bexec_step_internal_load:
      forall v k r r' o b ofs rs m rs' m',
      rs#BPC = Vint (Int.repr (Z.of_nat v)) ->
      find_instr v c = Some (Pload k r r' o) ->
      memory_region_map m Readable (sizeOp2chunk k) (Val.add rs#r' (Vint o)) b ofs ->
      exec_load k r (Vptr b ofs) rs m = Next rs' m' ->
      bstep c bl jit_blk ge (State rs m) E0 (State rs' m')

  | bexec_step_internal_store:
      forall v k r ri o b ofs rs m rs' m',
      rs#BPC = Vint (Int.repr (Z.of_nat v)) ->
      find_instr v c = Some (Pstore k r ri o) ->
      memory_region_map m Writable (sizeOp2chunk k) (Val.add rs#r (Vint o)) b ofs ->
      exec_store k ri (Vptr b ofs) rs m = Next rs' m' ->
      bstep c bl jit_blk ge (State rs m) E0 (State rs' m')


  | bexec_step_external: (**r call instruction *)
      forall v s sg ef args res rs m t rs' m',
      rs#BPC = Vint (Int.repr (Z.of_nat v)) ->
      find_instr v c = Some (Pcall s sg) ->
      _bpf_get_call s ge = Some (AST.External ef) ->
      args = (rs#R1 :: rs#R2 :: rs#R3 :: rs#R4 :: rs#R5 :: nil) ->
      external_call ef ge args m t (Vint res) m' ->
      rs' = nextinstr (rs # R0 <- (Vint res)) ->
      bstep c bl jit_blk ge (State rs m) t (State rs' m').

End RELSEM_B.