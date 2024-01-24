From Coq Require Import List ZArith.
Import ListNotations.
From dx Require Import ResultMonad IR.
From bpf.comm Require Import MemRegion Regs rBPFAST rBPFValues.

From compcert Require Import Coqlib Values Clight Memory Integers.

From bpf.clightlogic Require Import clight_exec Clightlogic CommonLemma CorrectRel.

From bpf.jit.jitclight Require Import havm_interpreter.
From bpf.jit.havm Require Import HAVMState HAVMMonadOp.

From bpf.jit.simulation Require Import MatchStateComm HAVMMatchState InterpreterRel.

(*
Check exec_function.
exec_function
     : val -> M val
*)

Section Exec_function.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Definition args : list Type := [(val:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := exec_function.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_exec_function.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    (dcons (fun x => StateLess _ (is_state_handle))
      (dcons (fun x => StateLess _ (eq x))
                (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv hybrid_state := fun r  => StateLess _ (val32_correct r).

  Axiom correct_function_exec_function : forall a, correct_function _ p args res f fn ModNothing false match_state match_arg_list match_res a.

End Exec_function.

Existing Instance correct_function_exec_function.
