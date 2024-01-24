From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory AST.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic clight_exec CommonLemma CorrectRel.

From bpf.jit.jitclight Require Import havm_interpreter.
From bpf.jit.havm Require Import HAVMState HAVMMonadOp.

From bpf.jit.simulation Require Import MatchStateComm HAVMMatchState InterpreterRel.


(**
Check load_mem.

load_mem
     : memory_chunk -> valu32_t -> M val64_t

 *)

Section Load_mem.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(memory_chunk:Type); val].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := load_mem.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_load_mem.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    dcons (fun x => StateLess _ is_state_handle)
          (dcons (fun ck => StateLess _ (match_chunk ck))
         (dcons (fun x => StateLess _ (eq x))
            (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv hybrid_state := fun x => StateLess _ (val32_correct x).

  Instance correct_function_load_mem : forall a, correct_function _ p args res f fn ModNothing false match_state match_arg_list match_res a.
Proof.
  correct_function_from_body args.
  correct_body.
  unfold f, load_mem, HAVMState.load_mem, Mem.loadv, INV, app.
  repeat intro.
  get_invariant _st.
  get_invariant _chunk.
  get_invariant _addr.
  unfold eval_inv, is_state_handle in c1.
  unfold eval_inv, match_chunk in c2.
  unfold eval_inv in c3.
  subst.

  unfold rBPFAST.memory_chunk_to_valu32, rBPFAST.well_chunk_Z in p1.
  unfold match_res, val32_correct.

  assert (Hload_implies: forall v,
    Mem.loadv c (bpf_m st) v1 =  Some v -> Mem.loadv c m v1 = Some v). {
    unfold Mem.loadv.
    intros.
    destruct v1; try inversion H0.
    rewrite H2.
    eapply match_state_implies_loadv_equal; eauto.
  }
  destruct c, v1; try constructor.
  - (**r c = Mint8unsigned *)
    destruct Mem.load eqn: Hload; try constructor.
    destruct v eqn: Hv_eq; try constructor.
    intros; exists (Vint i0); exists m, Events.E0.
    (**r v = Vint i0 *)
    split_and.
    + forward_star.
      change (Int.unsigned (Int.repr 1)) with 1%Z.
      simpl.
      unfold step2.
      forward_star.
      forward_star.
      * unfold Mem.loadv in *.
        rewrite <- Hv_eq in Hload.
        specialize (Hload_implies v Hload).
        apply Hload_implies.
      * rewrite Hv_eq; simpl.
        unfold Cop.sem_cast; simpl.
        reflexivity.
      * simpl. subst v.
        forward_star.
    + simpl. split_and; auto.
      eexists ; reflexivity.
    + constructor.
      simpl. auto.
    + auto.
    + apply unmodifies_effect_refl.
  - (**r c = Mint16unsigned *)
    destruct Mem.load eqn: Hload; try constructor.
    destruct v eqn: Hv_eq; try constructor.
    intros; exists (Vint i0); exists m, Events.E0.
    split_and; auto.
    + forward_star.
      change (Int.unsigned (Int.repr 2)) with 2%Z.
      simpl.
      unfold step2.
      forward_star.
      forward_star.
      * unfold Mem.loadv in *.
        rewrite <- Hv_eq in Hload.
        specialize (Hload_implies v Hload).
        apply Hload_implies.
      * rewrite Hv_eq; simpl.
        unfold Cop.sem_cast; simpl.
        reflexivity.
      * simpl. subst v.
        forward_star.
    + simpl. split ; eauto.
    + constructor; simpl; auto.
    + apply unmodifies_effect_refl.

  - (**r c = Mint32 *)
    destruct Mem.load eqn: Hload; try constructor.
    destruct v eqn: Hv_eq; try constructor.
    intros; exists (Vint i0); exists m, Events.E0.
    split_and; auto.
    + forward_star.
      change (Int.unsigned (Int.repr 4)) with 4%Z.
      simpl.
      unfold step2.
      forward_star.
      forward_star.
      unfold Mem.loadv in *.
      rewrite <- Hv_eq in Hload.
      specialize (Hload_implies v Hload).
      apply Hload_implies.
      * rewrite Hv_eq; simpl.
        unfold Cop.sem_cast; simpl.
        reflexivity.
      * simpl. subst v.
        forward_star.
    + simpl. split ; eauto.
    + constructor; simpl; auto.
    + apply unmodifies_effect_refl.
Qed.

End Load_mem.

Existing Instance correct_function_load_mem.
