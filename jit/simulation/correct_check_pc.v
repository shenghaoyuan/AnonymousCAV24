From bpf.comm Require Import LemmaInt.
From Coq Require Import List Lia ZArith.
From compcert Require Import Coqlib Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma.

From bpf.jit.jitclight Require Import havm_interpreter.
From bpf.jit.havm Require Import HAVMState HAVMMonadOp.

From bpf.jit.simulation Require Import MatchStateComm HAVMMatchState InterpreterRel.


(**
Check eval_pc.
eval_pc
     : M sint32_t
*)

Section Check_pc.
  Context {S : special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [].
  Definition res : Type := (bool:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := check_pc.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_check_pc.

Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
  dcons
    (fun x => StateLess _ is_state_handle)
    (DList.DNil _).


  (* [match_res] relates the Coq result and the C result *)

Definition match_res : res -> Inv hybrid_state := fun x  => StateLess _ (bool_correct x).

Instance correct_function_check_pc :
  forall a, correct_function _ p args res f fn ModNothing false (match_state ) match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    eapply correct_body_Sreturn_Some.
    repeat intro.
    unfold INV in H0.

    get_invariant _st.


    exists (Val.of_bool (Int.ltu (pc_loc st) (Int.repr (Z.of_nat (input_len st))))).
    split_and.
    -
      unfold exec_expr.
      rewrite p0.
      unfold eval_inv in c. unfold is_state_handle in c.
      subst.
      unfold exec_deref_loc.
      unfold Ctypes.access_mode.
      unfold typeof.
      unfold typeof; simpl;
      rewrite Ptrofs.add_zero_l;
      unfold align; simpl.
      inv H.
      change ((Ptrofs.unsigned (Ptrofs.repr (352 / 8))))%Z with 44%Z.
      unfold Mem.loadv in mpc.
      change (Ptrofs.unsigned (Ptrofs.repr 44)) with 44%Z in mpc.
      rewrite mpc.
      rewrite Ptrofs.add_zero_l.
      change (Ptrofs.unsigned (Ptrofs.repr (480 / 8))) with 60%Z.
      unfold Mem.loadv in mins_len.
      destruct mins_len as (Hload & Heq).
      change (Ptrofs.unsigned (Ptrofs.repr 60)) with 60%Z in Hload.
      rewrite Hload.
      unfold Cop.sem_cmp; simpl.
      unfold Cop.sem_binarith, Cop.sem_cast; simpl.
      f_equal.
    - simpl.
      unfold bool_correct.
      unfold HAVMState.check_pc.
      unfold Int.cmpu, Val.of_bool.
      unfold Vtrue, Vfalse.
      destruct Int.ltu; f_equal.
    - simpl.
      unfold Cop.sem_cast; simpl.
      unfold Val.of_bool.
      unfold Vtrue, Vfalse.
      destruct Int.ltu.
      + change (Int.eq Int.one Int.zero) with false.
        simpl. f_equal.
      + rewrite Int.eq_true. f_equal.
    - simpl.
      intro HV.
      unfold Ctypesdefs.tbool in HV.
      unfold Ctypesdefs.tint, Val.of_bool, Vtrue, Vfalse.
      destruct Int.ltu; eapply Cop.val_casted_int; eauto.
  Qed.

End Check_pc.

Existing  Instance correct_function_check_pc.
