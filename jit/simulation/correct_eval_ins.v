From bpf.comm Require Import LemmaInt ListAsArray.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma.

From bpf.jit.jitclight Require Import havm_interpreter.
From bpf.jit.havm Require Import HAVMState HAVMMonadOp.

From bpf.jit.simulation Require Import MatchStateComm HAVMMatchState InterpreterRel.


(**
Check eval_ins.
eval_ins
     : int -> M int64
*)

Section Eval_ins.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [].
  Definition res : Type := (int64:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := eval_ins.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_eval_ins.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    dcons (fun x => StateLess _ is_state_handle) (DList.DNil _).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv hybrid_state := fun x  => StateLess _ (int64_correct x).

  Instance correct_function_eval_ins : forall a, correct_function _ p args res f fn ModNothing false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.
    unfold f; simpl.
    destruct eval_ins eqn: Heval_ins; [| constructor].
    destruct p0.
    intros.
    unfold INV in H.
    get_invariant _st.
    unfold eval_inv, is_state_handle in c.
    subst.

    (** we need to get the value of pc in the memory *)
    assert (MS':=MS).
    destruct MS. clear - MS' p0 Heval_ins mpc mins_len mins.
    destruct mins_len as (Hload_eq & Hge).
    destruct mins as (Hins_eq & Hlen & Hle & Hmatch).
    eexists; exists m, Events.E0.

    split_and; auto.
    {
      unfold step2.
      forward_star.
      - unfold Coqlib.align; rewrite Ptrofs.add_zero_l.
        simpl.
        unfold Mem.loadv in Hins_eq.
        apply Hins_eq.
      - unfold Coqlib.align; rewrite Ptrofs.add_zero_l.
        simpl.
        unfold Mem.loadv in mpc.
        apply mpc.
      - reflexivity.
      - fold Ptrofs.zero; rewrite Ptrofs.add_zero_l.
        simpl.
        unfold match_list_ins in Hmatch.
        unfold Ptrofs.mul.
        unfold Ptrofs.of_intu, Ptrofs.of_int.
        change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8%Z.
        change Ptrofs.max_unsigned with 4294967295%Z in Hle.
        unfold eval_ins in Heval_ins.
        context_destruct_if_inversion.
        unfold Int.cmp in Hcond.
        apply Clt_Zlt_unsigned in Hcond.
        rewrite Int.unsigned_repr in Hcond. 2:{
          change Int.max_unsigned with 4294967295%Z.
          lia.
        }
        rewrite Ptrofs.unsigned_repr with (z:= (Int.unsigned (pc_loc st)));
          [| change Ptrofs.max_unsigned with 4294967295%Z].
        2:{
          split; [| lia].
          apply Z.ge_le. apply Int_unsigned_ge_zero.
        }
        rewrite Ptrofs.unsigned_repr; [| change Ptrofs.max_unsigned with 4294967295%Z].
        2:{
          split; [ |lia].
          assert (Hge': (Int.unsigned (pc_loc st) >= 0)%Z) by (apply Int_unsigned_ge_zero).
          lia.
        }
        rewrite Hlen in Hmatch.
        assert (Hnat: (0 <= Z.to_nat (Int.unsigned (pc_loc st)) < input_len st)%nat) by lia.
        specialize (Hmatch _ Hnat); clear Hnat.
        unfold Mem.loadv in Hmatch.
        assert (Hnat: Z.of_nat (Z.to_nat (Int.unsigned (pc_loc st))) = Int.unsigned (pc_loc st)).
          { apply Z2Nat.id.  apply Z.ge_le. apply Int_unsigned_ge_zero. }
        rewrite Hnat in Hmatch; clear Hnat.
        rewrite Ptrofs.unsigned_repr in Hmatch; [| change Ptrofs.max_unsigned with 4294967295%Z].
        2:{
          split; [ |lia].
          assert (Hge': (Int.unsigned (pc_loc st) >= 0)%Z) by (apply Int_unsigned_ge_zero).
          lia.
        }
        subst.
        apply Hmatch.
      - unfold Cop.sem_cast, typeof; simpl.
        reflexivity.
      - forward_star.
    }
    {
      unfold int64_correct.
      unfold eval_ins in Heval_ins.
      context_destruct_if_inversion.
      unfold HAVMState.eval_ins, List64AsArray.index in H0.
      destruct nth_error eqn: Hins; inversion H0.
      subst.
      eapply nth_error_nth with (d:= Int64.zero) in Hins.
      rewrite <- Hins.
      reflexivity.
    }
    constructor.
    unfold eval_ins in Heval_ins.
    context_destruct_if_inversion.
    destruct HAVMState.eval_ins; inversion H0.
    subst.
    assumption.
    unfold eval_ins in Heval_ins.
    context_destruct_if_inversion.
    destruct HAVMState.eval_ins; inversion H0.
    reflexivity.
  Qed.

End Eval_ins.

Existing  Instance correct_function_eval_ins.
