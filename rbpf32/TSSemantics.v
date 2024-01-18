From compcert.lib Require Import Integers Coqlib Maps.
From compcert.common Require Import AST Values Events Globalenvs Memory Memtype.
From compcert.cfrontend Require Import Ctypes.
From compcert.backend Require Import Locations.
From compcert.arm Require Import ABinSem.
From Coq Require Import ZArith Lia List.

From bpf.rbpf32 Require Import TSSyntax TSDecode.

Open Scope Z_scope.
Import ListNotations.


(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain (but do not enforce)
  the convention that integer registers are mapped to values of
  type [Tint], float registers to values of type [Tfloat],
  and condition bits to either [Vzero] or [Vone]. *)

(** Conventional names for stack pointer ([SP]) *)


Section RELSEM.

Hypothesis _bpf_get_call: ident -> genv -> option fundef.
Hypothesis memory_region_map: mem -> permission -> memory_chunk -> val -> block -> ptrofs -> Prop.

(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual eBPF instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the eBPF reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above. *)

(** Execution of the instruction at [rs PC]. *)

Inductive step (c: code) (ge: genv): state -> trace -> state -> Prop :=
  | exec_step_alu32:
      forall v o r ri rs m rs' m',
      rs#BPC = Vint (Int.repr (Z.of_nat v)) ->
      find_instr v c = Some (Palu32 o r ri) ->
      exec_alu32 o r ri rs m = Next rs' m' ->
      step c ge (State rs m) E0 (State rs' m')

  | exec_step_jmp_always:
      forall v l rs m rs' m',
      rs#BPC = Vint (Int.repr (Z.of_nat v)) ->
      find_instr v c = Some (Pjmp l) ->
      goto_label c l rs m = Next rs' m' ->
      step c ge (State rs m) E0 (State rs' m')

  | exec_step_jmp_cond:
      forall v o r ri l rs m rs' m',
      rs#BPC = Vint (Int.repr (Z.of_nat v)) ->
      find_instr v c = Some (Pjmpcmp o r ri l) ->
      exec_branch c l rs m (eval_cmp o rs m r ri) = Next rs' m' ->
      step c ge (State rs m) E0 (State rs' m')

  | exec_step_internal_load:
      forall v k r r' o b ofs rs m rs' m',
      rs#BPC = Vint (Int.repr (Z.of_nat v)) ->
      find_instr v c = Some (Pload k r r' o) ->
      memory_region_map m Readable (sizeOp2chunk k) (Val.add rs#r' (Vint o)) b ofs ->
      max_ofs (Ptrofs.to_int ofs) k = true ->
      exec_load k r (Vptr b ofs) rs m = Next rs' m' ->
      step c ge (State rs m) E0 (State rs' m')

  | exec_step_internal_store:
      forall v k r ri o b ofs rs m rs' m',
      rs#BPC = Vint (Int.repr (Z.of_nat v)) ->
      find_instr v c = Some (Pstore k r ri o) ->
      memory_region_map m Writable (sizeOp2chunk k) (Val.add rs#r (Vint o)) b ofs ->
      max_ofs (Ptrofs.to_int ofs) k = true ->
      exec_store k ri (Vptr b ofs) rs m = Next rs' m' ->
      step c ge (State rs m) E0 (State rs' m')


  | exec_step_external: (**r call instruction *)
      forall v s sg ef args res rs m t rs' m',
      rs#BPC = Vint (Int.repr (Z.of_nat v)) ->
      find_instr v c = Some (Pcall s sg) ->
      _bpf_get_call s ge = Some (AST.External ef) ->
      args = (rs#R1 :: rs#R2 :: rs#R3 :: rs#R4 :: rs#R5 :: nil) ->
      external_call ef ge args m t (Vint res) m' ->
      rs' = nextinstr (rs # R0 <- (Vint res)) ->
      step c ge (State rs m) t (State rs' m').

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (c: code) (m: mem) (ptr: val): state -> Prop :=
  | initial_state_intro:
    let rs0 := (BPregmap.init Vzero)
      # R10 <- ptr in
    initial_state c m ptr (State rs0 m).

Inductive final_state (c: code) (ptr: val): state -> int -> Prop :=
  | final_state_intro: forall (rs: regset) m r v,
    rs#R0 = Vint r ->
    rs#R10 = ptr ->
    rs#BPC = Vint (Int.repr (Z.of_nat v)) ->
    find_instr v c = Some Pret ->
    final_state c ptr (State rs m) r.