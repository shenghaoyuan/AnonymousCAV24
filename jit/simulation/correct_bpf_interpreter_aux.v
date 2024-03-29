From Coq Require Import List ZArith.
Import ListNotations.
From dx Require Import ResultMonad IR.
From bpf.comm Require Import Flag MemRegion Flag Regs rBPFAST rBPFValues.

From compcert Require Import Coqlib Values AST Clight Memory Memtype Integers.

From bpf.clightlogic Require Import Clightlogic clight_exec CommonLemma CorrectRel.

From bpf.jit.simulation Require Import correct_upd_flag correct_check_pc correct_check_pc_incr correct_eval_flag correct_step.

From bpf.jit.jitclight Require Import havm_interpreter.
From bpf.jit.havm Require Import HAVMState HAVMMonadOp DxHAVMInterpreter.

From bpf.jit.simulation Require Import MatchStateComm HAVMMatchState InterpreterRel.

Open Scope Z_scope.


(**
Check bpf_interpreter_aux.
bpf_interpreter_aux
     : nat -> M unit
*)

Section Bpf_interpreter_aux.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := bpf_interpreter_aux.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_bpf_interpreter_aux.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list :DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    (dcons (fun _ => StateLess _ is_state_handle)
      (dcons (stateless nat_correct)
                    (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv hybrid_state := fun x => StateLess _ (eq Vundef).


Lemma bpf_interpreter_aux_eq: forall n,
  bpf_interpreter_aux n =
    if Nat.eqb n 0 then bindM (upd_flag BPF_ILLEGAL_LEN) (fun _ : unit => returnM tt)
    else
      (bindM check_pc (fun b0 =>
        if b0 then
        (bindM step (fun _ =>
          (bindM eval_flag (fun f =>
            if flag_eq f BPF_OK then
              (bindM check_pc_incr (fun b1 =>
                if b1 then
                  (bindM (upd_pc Int.one) (fun _ =>
                    bpf_interpreter_aux (Init.Nat.pred n)))
                else
                  bindM (upd_flag BPF_ILLEGAL_LEN) (fun _ : unit => returnM tt)))
            else
              returnM tt))))
        else
          bindM (upd_flag BPF_ILLEGAL_LEN) (fun _ : unit => returnM tt))).
Proof.
  destruct n.
  - simpl. intros; reflexivity.
  - intros.
    simpl.
    reflexivity.
Qed.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Lemma mod_eq : forall (x y:Z), (x >= 0 -> y > 0 -> x mod y = x -> x < y)%Z.
Proof.
  intros.
  zify.
  intuition subst ; try lia.
Qed.

  Instance correct_function_bpf_interpreter_aux : forall a, correct_function _ p args res f fn ModSomething false match_state match_arg_list match_res a.
  Proof.
    intros.
    unfold args in a.
    car_cdr.
    induction c.
    {
      intros.
      correct_function_from_body args.
      unfold f. unfold cl_app. intros. rewrite bpf_interpreter_aux_eq.
      remember (0 =? 0)%nat as cmp.
      simpl.
      rewrite Heqcmp.
      correct_forward. unfold bindM, returnM.
      correct_forward.

      get_invariant _st.
      exists (v ::
              (Vint (Int.repr 6)) :: nil). (**r star here *)
      unfold map_opt, exec_expr.
      rewrite p0.
      unfold Cop.sem_unary_operation; simpl.
      split.
      reflexivity.
      intros.
      unfold stateless, flag_correct, int_of_flag; simpl.
      intuition congruence.
      intros.

      (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
      correct_forward.
      unfold match_res.

      unfold eval_inv; auto.

      inversion Hcnd.

      get_invariant _fuel.
      unfold exec_expr.
      rewrite p0.
      unfold stateless, nat_correct in c.
      destruct c as (c & _).
      rewrite <- c.
      unfold Cop.sem_binary_operation, typeof; simpl.
      unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
      unfold Cop.sem_cast; simpl.
      reflexivity.
    }

    intros.
    correct_function_from_body args.
    correct_body.
    unfold f, cl_app.
    rewrite bpf_interpreter_aux_eq.
    correct_forward.
    inversion Hcnd.
    simpl.
    apply correct_statement_seq_set with (match_res1 := stateless nat_correct c).

    intros Hst H; simpl in H.
    get_invariant _fuel.
    unfold eval_inv, stateless, nat_correct in c0.
    destruct c0 as (c0 & Hc0_range).
    subst.
    eexists.
    split.
    {
      unfold exec_expr.
      rewrite p0.
      unfold Cop.sem_binary_operation, Cop.sem_sub; simpl.
      unfold Cop.sem_binarith; simpl.
      unfold Cop.sem_cast; simpl.
      unfold Int.sub.
      fold Int.one; rewrite Int.unsigned_one.
      rewrite Zpos_P_of_succ_nat.
      rewrite <- Nat2Z.inj_succ.
      rewrite Int.unsigned_repr; [ | lia].
      rewrite Nat2Z.inj_succ.
      rewrite <- Z.add_1_r.
      rewrite Z.add_simpl_r.
      reflexivity.
    }
    split.
    {
      unfold eval_inv, stateless, nat_correct.
      split. reflexivity. lia.
    }
    constructor.
    simpl.
    reflexivity.
    prove_in_inv.

    intros. unfold bindM, returnM.

    (**r correct_body _ _ (bindM (eval_pc _ _) ... *)
    correct_forward.

    get_invariant _st.
    exists (v::nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0; reflexivity.
    simpl;intros.
    intuition eauto.
    intros.

    correct_forward.
    {
      correct_forward.

      get_invariant _st.
      exists (v::nil).
      split.
      unfold map_opt, exec_expr.
      rewrite p0; reflexivity.
      simpl;intros.
      intuition eauto.
      intros.

      correct_forward.

      get_invariant _st.
      exists (v::nil).
      split.
      unfold map_opt, exec_expr.
      rewrite p0; reflexivity.
      simpl;intros.
      intuition eauto.
      intros.

      correct_forward.
      {
        - (**r correct_body _ _ (bindM (check_pc_incr _ _) ... *)
          correct_forward.

          get_invariant _st.
          exists (v :: nil).
          split.
          unfold map_opt, exec_expr.
          rewrite p0; reflexivity.
          simpl;intros.
          intuition eauto.
          intros.

          correct_forward.
          + correct_forward.

            get_invariant _st.
            exists (v:: Vint (Int.repr 1)::nil).
            split.
            unfold map_opt, exec_expr.
            rewrite p0; reflexivity.
            simpl;intros.
            intuition eauto.
            unfold uint32_correct; simpl.
            split; [auto | ]. replace Int.max_unsigned with 4294967295 by reflexivity; lia.
            intros.

          assert (Heq: bpf_interpreter_aux c = bindM (bpf_interpreter_aux c) (fun _ : unit => returnM tt)). {
            clear.
            unfold bindM, returnM.
            induction c.
            simpl. unfold upd_flag; reflexivity.
            simpl.
            unfold bpf_interpreter_aux.
            unfold bindM. unfold Monad.bindM, Monad.returnM in *.
            apply Coq.Logic.FunctionalExtensionality.functional_extensionality; intro.
            destruct check_pc; [| reflexivity].
            destruct p0.
            destruct b; [| reflexivity].
            destruct step; [| reflexivity].
            destruct p0.
            destruct eval_flag; [| reflexivity].
            destruct p0.
            destruct flag_eq; [| reflexivity].
            destruct check_pc_incr; [| reflexivity].
            destruct p0.
            destruct b0; [| reflexivity].
            destruct upd_pc; [| reflexivity].
            destruct p0.
            unfold bpf_interpreter_aux in IHc.
            unfold bindM in IHc. unfold Monad.bindM, Monad.returnM in *.
            rewrite IHc.

            destruct (fix bpf_interpreter_aux (fuel : nat) : M  unit :=
         match fuel with
         | 0%nat => upd_flag BPF_ILLEGAL_LEN
         | Datatypes.S fuel0 =>
             fun st : hybrid_state =>
             match check_pc st with
             | Some (x', st') =>
                 (if x'
                  then
                   fun st0 : hybrid_state =>
                   match step st0 with
                   | Some (_, st'0) =>
                       match eval_flag st'0 with
                       | Some (x'1, st'1) =>
                           (if flag_eq x'1 BPF_OK
                            then
                             fun st1 : hybrid_state =>
                             match check_pc_incr st1 with
                             | Some (x'2, st'2) =>
                                 (if x'2
                                  then
                                   fun st2 : hybrid_state =>
                                   match upd_pc Int.one st2 with
                                   | Some (_, st'3) => bpf_interpreter_aux fuel0 st'3
                                   | None => None
                                   end
                                  else upd_flag BPF_ILLEGAL_LEN) st'2
                             | None => None
                             end
                            else returnM tt) st'1
                       | None => None
                       end
                   | None => None
                   end
                  else upd_flag BPF_ILLEGAL_LEN) st'
             | None => None
             end
         end); try reflexivity.
            destruct p0.
            auto.
            }
            rewrite Heq; clear Heq. unfold bindM, returnM.
            correct_forward.

            get_invariant _st.
            get_invariant _fuel0.
            exists (v::v0::nil).
            split.
            unfold map_opt, exec_expr.
            rewrite p0, p1; reflexivity.
            intros; simpl.
            intuition eauto.

            intros.
            correct_forward.
            unfold eval_inv.
            unfold match_res.
            reflexivity.
          + correct_forward.

            get_invariant _st.
            exists (v::(Vint (Int.repr 6)) :: nil).
            split.
            unfold map_opt, exec_expr.
            rewrite p0; reflexivity.
            simpl;intros.
            unfold stateless, flag_correct, int_of_flag, Z_of_flag.
            intuition eauto.
            intros.

            correct_forward.
            unfold eval_inv.
            unfold match_res.
            reflexivity.
          + get_invariant _b1.
            unfold exec_expr. rewrite p0.
            unfold eval_inv, correct_check_pc_incr.match_res, bool_correct in c0.
            subst.
            unfold Val.of_bool, Vtrue, Vfalse.
            destruct x2; f_equal.
      }

      correct_forward.

      unfold eval_inv.
      unfold match_res.
      reflexivity.

      get_invariant _f.
      unfold exec_expr.
      rewrite p0.
      unfold eval_inv, correct_eval_flag.match_res, flag_correct in c0.
      rewrite c0.
      unfold Cop.sem_binary_operation.
      unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
      unfold flag_eq, int_of_flag.
      unfold Val.of_bool, Vtrue, Vfalse.
      destruct x1 eqn: Heq_x2; simpl; try reflexivity.
    }

    correct_forward.

    get_invariant _st.
    exists (v::(Vint (Int.repr 6)) :: nil).
    split.
    unfold map_opt, exec_expr.
    rewrite p0; reflexivity.
    simpl;intros.
    unfold stateless, flag_correct, int_of_flag, Z_of_flag.
    intuition eauto.
    intros.

    correct_forward.

    unfold eval_inv.
    unfold match_res.
    reflexivity.

    get_invariant _b0.
    unfold exec_expr. rewrite p0.
    unfold eval_inv, correct_check_pc.match_res, bool_correct in c0.
    subst.
    unfold Val.of_bool, Vtrue, Vfalse.
    destruct x; f_equal.

    get_invariant _fuel.
    unfold stateless, nat_correct in c0.
    destruct c0 as (Hv_eq & Hrange).
    unfold exec_expr.
    rewrite p0.
    simpl.
    rewrite <- Hv_eq.
    unfold Cop.sem_cmp, Cop.sem_binarith, Val.of_bool, Vfalse; simpl.
    unfold Cop.sem_cast; simpl.
    unfold Int.eq.
    change (Int.unsigned (Int.repr 0)) with 0.
    rewrite Int.unsigned_repr;[ | lia].
    assert (Hneq: (Z.succ (Z.of_nat c)) <> 0). {
      lia.
    }
    eapply zeq_false with (a:= true) (b:= false) in Hneq.
    rewrite Zpos_P_of_succ_nat.
    rewrite Hneq.
    reflexivity.
Qed.

End Bpf_interpreter_aux.

Close Scope Z_scope.

Existing Instance correct_function_bpf_interpreter_aux.
