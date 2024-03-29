From Coq Require Import List ZArith.
Import ListNotations.
From dx Require Import ResultMonad IR.
From bpf.comm Require Import MemRegion Regs rBPFAST rBPFValues.

From compcert Require Import Coqlib Values Clight Memory Integers.

From bpf.clightlogic Require Import Clightlogic clight_exec CommonLemma CorrectRel.

From bpf.jit.jitclight Require Import havm_interpreter.
From bpf.jit.havm Require Import HAVMState HAVMMonadOp.

From bpf.jit.simulation Require Import MatchStateComm HAVMMatchState InterpreterRel.


(*
Check _bpf_get_call.
_bpf_get_call
     : val -> M val
*)

Section Bpf_get_call.
  Context {S: special_blocks}.
  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Definition args : list Type := [(val:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := _bpf_get_call.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f__bpf_get_call.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv hybrid_state) args :=
      (dcons (fun x => StateLess hybrid_state (val32_correct x))
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv hybrid_state := fun r  => StateLess hybrid_state (eq r).

  Axiom correct_function__bpf_get_call : forall a, correct_function hybrid_state p args res f fn ModNothing true match_state match_arg_list match_res a.

End Bpf_get_call.

Existing Instance correct_function__bpf_get_call.
