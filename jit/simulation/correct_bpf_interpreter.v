From bpf.comm Require Import Flag MemRegion.

From Coq Require Import List ZArith.
From compcert Require Import Integers Values Clight Memory AST.
From compcert Require Import Coqlib.
Import ListNotations.

From bpf.clightlogic Require Import clight_exec Clightlogic CorrectRel CommonLemma.

From bpf.jit.simulation Require Import correct_upd_reg correct_bpf_interpreter_aux correct_eval_flag correct_eval_reg.

From bpf.jit.jitclight Require Import havm_interpreter.
From bpf.jit.havm Require Import HAVMState HAVMMonadOp DxHAVMInterpreter.

From bpf.jit.simulation Require Import MatchStateComm HAVMMatchState InterpreterRel.


(**
Check bpf_interpreter.
bpf_interpreter
     : nat -> M val
*)

Section Bpf_interpreter.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (val:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := havm_interpreter.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_havm_interpreter.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list :DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    (dcons (fun _ => StateLess _ is_state_handle)
      (dcons (stateless nat_correct)
        (dcons (stateless val32_correct)
                    (DList.DNil _)))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv hybrid_state := fun x => StateLess _ (val32_correct x).

  Instance correct_function_bpf_interpreter : forall a, correct_function _ p args res f fn ModSomething false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f, app.
    unfold havm_interpreter. unfold bindM, returnM.
    correct_forward.

    get_invariant _st.
    get_invariant _fuel.
    get_invariant _ctx_ptr.
    exists (v::Vint (Int.repr 1)::v1::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0,p2; reflexivity.
    intros; simpl.
    intuition eauto.
    unfold reg_correct; simpl. auto.

    intros.

    correct_forward.

    get_invariant _st.
    get_invariant _fuel.
    exists (v::v0::nil).
    split.
    unfold map_opt, exec_expr. rewrite p0,p1; reflexivity.
    intros; simpl.
    intuition eauto.
    intros.

    correct_forward.
    {
      get_invariant _st.
      exists (v::nil).
      split.
      unfold map_opt, exec_expr. rewrite p0; reflexivity.
      intros; simpl.
      unfold stateless, reg_correct.
      intuition eauto.
    }

    intros.
    correct_forward; eauto.
    - correct_forward.

      get_invariant _st.
      unfold eval_inv, correct_eval_reg.match_res, is_state_handle in c1.
      simpl. rewrite p0.
      exists [v; Vint (Int.repr 0)].
      split; auto.
      intros. simpl.
      unfold is_state_handle, reg_correct.
      intuition eauto.
      intros.

      correct_forward.

      get_invariant _res.
      simpl. rewrite p0.  exists v.
      split.
      reflexivity.
      intuition eauto.
      unfold Cop.sem_cast; simpl.
      unfold eval_inv, correct_eval_reg.match_res, val32_correct in c1.
      destruct c1 as (Hv & Hvi & Hvi_eq).
      subst.
      f_equal.
    -
      correct_forward.
      eexists.
      split.
      unfold exec_expr; simpl.
      reflexivity.
      split.
      unfold match_res, val32_correct, DxValues.val32_zero, Vzero; simpl.
      intuition eauto.
      split.
      reflexivity.
      intros.
      constructor.
      simpl.
      f_equal.

    -
      get_invariant _f.
      unfold exec_expr.
      rewrite p0.
      unfold eval_inv, correct_eval_flag.match_res, flag_correct in c1.
      rewrite c1.
      unfold Cop.sem_binary_operation, Val.of_bool, int_of_flag, Z_of_flag; simpl.
      destruct x1; reflexivity.
Qed.

End Bpf_interpreter.

Existing Instance correct_function_bpf_interpreter.
