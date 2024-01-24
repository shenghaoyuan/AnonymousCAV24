From bpf.comm Require Import Flag.

From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma CommonLib.

From bpf.jit.jitclight Require Import havm_interpreter.
From bpf.jit.havm Require Import HAVMState HAVMMonadOp.

From bpf.jit.simulation Require Import MatchStateComm HAVMMatchState InterpreterRel.



Section Eval_flag.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [].
  Definition res : Type := (bpf_flag:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := eval_flag.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_flag.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    dcons (fun x => StateLess _ (is_state_handle)) (DList.DNil _).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv hybrid_state := fun x => StateLess _ (flag_correct x).

  Instance correct_function_eval_flag : forall a, correct_function _ p args res f fn ModNothing false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.
    unfold INV in H.
    get_invariant _st.
    unfold eval_inv, is_state_handle in c.
    subst.

    (** we need to get the value of pc in the memory *)
    destruct MS.
    unfold Mem.loadv in mflags.
    (** pc \in [ (state_block,0), (state_block,8) ) *)
    (**according to the type:
         static int eval_flag(struct bpf_state* st)
       1. return value should be Vint
       2. the memory is same
      *)
    exists (Vint (int_of_flag (flag st))), m, Events.E0.

    split_and; unfold step2.
    - (* goal: Smallstep.star  _ _ (State _ (Ssequence ... *)
      repeat forward_star.

      + unfold Coqlib.align; simpl.
        rewrite Ptrofs.add_zero_l.
        change (Ptrofs.unsigned (Ptrofs.repr (384 / 8))) with (Ptrofs.unsigned (Ptrofs.repr 48)).
        rewrite mflags; reflexivity.
      + econstructor; eauto.
    - simpl.
      constructor.
    - constructor.
      reflexivity.
    - constructor; auto.
    - apply unmodifies_effect_refl.
  Qed.

End Eval_flag.

Existing  Instance correct_function_eval_flag.
