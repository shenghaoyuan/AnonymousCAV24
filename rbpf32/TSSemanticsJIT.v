From compcert.lib Require Import Integers Coqlib Maps.
From compcert.common Require Import AST Values Events Globalenvs Memory Memtype.
From compcert.cfrontend Require Import Ctypes.
From compcert.backend Require Import Locations.
From compcert.arm Require Import AsmSyntax ABinSem.
From Coq Require Import ZArith Lia List.

From bpf.comm Require Import JITCall.
From bpf.rbpf32 Require Import TSSyntax TSDecode JITConfig.

Open Scope Z_scope.
Import ListNotations.


(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain (but do not enforce)
  the convention that integer registers are mapped to values of
  type [Tint], float registers to values of type [Tfloat],
  and condition bits to either [Vzero] or [Vone]. *)

(** Conventional names for stack pointer ([SP]) *)

Fixpoint find_key_value (kv: list (nat * nat)) (key: nat): option nat :=
  match kv with
  | [] => None
  | (k, v) :: tl =>
    if Nat.eqb k key then
      Some v
    else
      find_key_value tl key
  end.

Section RELSEMJIT.

Hypothesis _bpf_get_call: ident -> genv -> option fundef.
Hypothesis memory_region_map: mem -> permission -> memory_chunk -> val -> block -> ptrofs -> Prop.
Hypothesis key_value: list (nat * nat).

(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual eBPF instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the eBPF reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above. *)

Inductive pair_state :=
| PState: bool ->
  regset ->       (**r rBPF register map *)
  aregset ->      (**r ARM register map *)
  astack -> block (**r stack block *) ->
  block (**r jitted arm code block *) ->
  mem -> pair_state.

(** Execution of the instruction at [rs PC]. *)

Inductive step (c: code) (st_blk: block) (ge: genv): pair_state -> trace -> pair_state -> Prop :=

  | exec_step_jit_init:
      forall rs jit_blk v o r ri m m1 m2 ofs (ars: aregset) stk stkb ars' stk' stkb' m',
      rs#BPC = Vint v ->
      find_instr (Z.to_nat (Int.unsigned v)) c = Some (Palu32 o r ri) ->
      find_key_value key_value (Z.to_nat (Int.unsigned v)) = Some ofs ->
      Mem.alloc m 0 state_block_size = (m1, st_blk) ->
      copy_to rs st_blk m1 = Some m2 -> (*
      oldsp = ars IR13 -> (**r maybe we don't need it *) *)
      init_state compcertbin_signature stack_block_size Ptrofs.zero
        [ Val.add (Vptr jit_blk Ptrofs.zero)
                  (Vint (Int.mul (Int.repr (Z.of_nat ofs)) (Int.repr 2)));
          (Vptr st_blk Ptrofs.zero)] m2 = ANext ars' stk' stkb' m' ->
      step c st_blk ge  (PState false rs ars stk stkb jit_blk m) E0
                        (PState true rs ars' stk' stkb' jit_blk m')

  | exec_step_jit_final:
      forall rs jit_blk v m ars stk stkb rs' m',
      rs#BPC = Vint v ->
      is_final_state ars = true -> (**r have to say `is_definedb v && has_rettypeb v` *)
      copy_from rs st_blk m = Some rs' ->
      Mem.free m st_blk 0 state_block_size = Some m' -> (**r maybe not *)
      step c st_blk ge  (PState true rs ars stk stkb jit_blk m) E0
                        (PState false rs' ars stk stkb jit_blk m')

  | exec_step_jit:
      forall rs jit_blk v m i sz ars stk stkb ars' stk' stkb' m',
      rs#BPC = Vint v ->
      ABinSem.find_instr (ars AsmSyntax.PC) m = Some (i, sz) ->
      aexec_instr sz i ars stk stkb m = ANext ars' stk' stkb' m' ->
      step c st_blk ge  (PState true rs ars stk stkb jit_blk m) E0
                        (PState true rs ars' stk' stkb' jit_blk m')

  | exec_step_jmp_always:
      forall v l rs m rs' m' ars stk stkb jit_blk,
      rs#BPC = Vint v ->
      find_instr (Z.to_nat (Int.unsigned v)) c = Some (Pjmp l) ->
      goto_label c l rs m = Next rs' m' ->
      step c st_blk ge  (PState false rs ars stk stkb jit_blk m) E0
                        (PState false rs' ars stk stkb jit_blk m')

  | exec_step_jmp_cond:
      forall v o r ri l rs m rs' m' ars stk stkb jit_blk,
      rs#BPC = Vint v ->
      find_instr (Z.to_nat (Int.unsigned v)) c = Some (Pjmpcmp o r ri l) ->
      exec_branch c l rs m (eval_cmp o rs m r ri) = Next rs' m' ->
      step c st_blk ge  (PState false rs ars stk stkb jit_blk m) E0
                        (PState false rs' ars stk stkb jit_blk m')

  | exec_step_internal_load:
      forall v k r r' o b ofs rs m rs' m' ars stk stkb jit_blk,
      rs#BPC = Vint v ->
      find_instr (Z.to_nat (Int.unsigned v)) c = Some (Pload k r r' o) ->
      memory_region_map m Readable (sizeOp2chunk k) (Val.add rs#r' (Vint o)) b ofs ->
      max_ofs (Ptrofs.to_int ofs) k = true ->
      exec_load k r (Vptr b ofs) rs m = Next rs' m' ->
      step c st_blk ge  (PState false rs ars stk stkb jit_blk m) E0
                        (PState false rs' ars stk stkb jit_blk m')

  | exec_step_internal_store:
      forall v k r ri o b ofs rs m rs' m' ars stk stkb jit_blk,
      rs#BPC = Vint v ->
      find_instr (Z.to_nat (Int.unsigned v)) c = Some (Pstore k r ri o) ->
      memory_region_map m Writable (sizeOp2chunk k) (Val.add rs#r (Vint o)) b ofs ->
      max_ofs (Ptrofs.to_int ofs) k = true ->
      exec_store k ri (Vptr b ofs) rs m = Next rs' m' ->
      step c st_blk ge  (PState false rs ars stk stkb jit_blk m) E0
                        (PState false rs' ars stk stkb jit_blk m')


  | exec_step_external: (**r call instruction *)
      forall v s sg ef args res rs m t rs' m' ars stk stkb jit_blk,
      rs#BPC = Vint v ->
      find_instr (Z.to_nat (Int.unsigned v)) c = Some (Pcall s sg) ->
      _bpf_get_call s ge = Some (AST.External ef) ->
      args = (rs#R1 :: rs#R2 :: rs#R3 :: rs#R4 :: rs#R5 :: nil) ->
      external_call ef ge args m t res m' ->
      rs' = nextinstr (rs # R0 <- res) ->
      step c st_blk ge  (PState false rs ars stk stkb jit_blk m) t
                        (PState false rs' ars stk stkb jit_blk m').

End RELSEMJIT.

(** Execution of whole programs. *)

Inductive initial_state (c: code) (m: mem) (ptr: val): pair_state -> Prop :=
  | initial_state_intro: forall ars stk stkb jit_blk,
    let rs0 := (BPregmap.init Vzero) # R10 <- ptr in
    initial_state c m ptr (PState false rs0 ars stk stkb jit_blk m).

Inductive final_state (c: code) (ptr: val): pair_state -> int -> Prop :=
  | final_state_intro: forall (rs: regset) m r v ars stk stkb jit_blk,
    rs#R0 = Vint r ->
    rs#R10 = ptr ->
    rs#BPC = Vint v ->
    find_instr (Z.to_nat (Int.unsigned v)) c = Some Pret ->
    final_state c ptr (PState false rs ars stk stkb jit_blk m) r.