From Coq Require Import List Lia ZArith.
From compcert Require Import Coqlib Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma.

From bpf.jit.jitclight Require Import havm_interpreter.
From bpf.jit.havm Require Import HAVMState HAVMMonadOp DxHAVMInterpreter.

From bpf.jit.simulation Require Import MatchStateComm HAVMMatchState InterpreterRel.

From bpf.jit.simulation Require Import correct_get_immediate correct_get_src correct_eval_reg.


(**
Check get_src32.
get_src32
     : nat -> int64 -> M val

 *)

Open Scope Z_scope.

Section Get_src32.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type); (int64:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_src32.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_src32.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    dcons (fun x => StateLess _ is_state_handle)
      (dcons (fun x => StateLess _ (opcode_correct x))
        (dcons (fun x => StateLess _ (int64_correct x))
                    (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv hybrid_state := fun x  => StateLess _ (val32_correct x).

  Instance correct_function_get_src32 : forall a, correct_function _ p args res f fn ModNothing false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f, cl_app, get_src32.
    intros.
    

    correct_forward.
    - unfold bindM, returnM.
      correct_forward.

      get_invariant _ins.
      exists (v::nil).
      split.
      unfold map_opt, exec_expr. rewrite p0.
      reflexivity.
      intros; simpl. (**r TODO: need a verifier information ... *)
      tauto.

      intros.
      correct_forward.
      get_invariant _imm.
      unfold eval_inv,correct_get_immediate.match_res, sint32_correct in c1.
      destruct c1 as (c1 & c1_range).
      eexists ; split_and.
      { unfold exec_expr, empty_env.
        rewrite p0; reflexivity.
      }
      { unfold eval_inv,match_res, rBPFValues.sint32_to_vint, val32_correct; simpl. eauto.
      }
      { subst. reflexivity. }
      {simpl ; auto.
      }
    - unfold bindM.
      correct_forward.

      get_invariant _ins.
      exists (v::nil).
      split.
      unfold map_opt, exec_expr. rewrite p0.
      reflexivity.
      intros; simpl.
      unfold int64_correct.
      tauto.

      intros.
      correct_forward.

      get_invariant _st.
      get_invariant _src.
      exists (v::v0::nil).
      split_and.
      { unfold map_opt, exec_expr. rewrite p0, p1.
        reflexivity. }
      { intros; simpl.
        unfold eval_inv, correct_get_src.match_res in *.
        tauto.
      }
      intros. unfold returnM.
      correct_forward.

      get_invariant _v.
      destruct c1 as (Hv_eq & vl & Hvl_eq).
      subst.
      eexists. split_and.
      { unfold exec_expr, empty_env.
        rewrite p0; reflexivity. }
      { unfold match_res; simpl. unfold val32_correct.
        eauto. }
      reflexivity.
      simpl. auto.
    - get_invariant _x.
      unfold exec_expr.
      rewrite p0.
      simpl.
      unfold eval_inv, opcode_correct in c1.
      destruct c1 as (Hv_eq & Hc_le); subst.
      unfold Cop.sem_and, Cop.sem_cmp, Cop.sem_binarith, Cop.sem_cast; simpl.
      reflexivity.
  Qed.

End Get_src32.
Close Scope Z_scope.

Existing Instance correct_function_get_src32.
