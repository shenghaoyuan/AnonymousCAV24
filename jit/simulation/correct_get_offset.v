From bpf.comm Require Import Regs BinrBPF.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma.

From bpf.jit.jitclight Require Import havm_interpreter.
From bpf.jit.havm Require Import HAVMState HAVMMonadOp.

From bpf.jit.simulation Require Import MatchStateComm HAVMMatchState InterpreterRel.

(**
Check get_offset.
get_offset
     : int64 -> M int

 *)

Open Scope Z_scope.

Section Get_offset.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int64:Type)].
  Definition res : Type := (int:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_offset.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_offset.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    (dcons (fun x => StateLess _ (int64_correct x))
                    (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv hybrid_state := fun x  => StateLess _ (sint32_correct x).

  Instance correct_function_get_offset : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _ins.

    unfold eval_inv, int64_correct in c0.
    subst.

    eexists; exists m, Events.E0.

    split_and; auto.
    {
      repeat forward_star.
    }
    {
      unfold match_res, sint32_correct, BinrBPF.get_offset; simpl.
      (**r according to the clight representation, we delete the self-defined library int16 in order to simplify the proof here *)
      split;[reflexivity | apply Int.signed_range].
    }
    constructor;auto.
    apply unmodifies_effect_refl.
  Qed.

End Get_offset.
Close Scope Z_scope.

Existing Instance correct_function_get_offset.
