From bpf.monadicmodel Require Import Opcode.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma CommonLemmaNat.

From bpf.jit.jitclight Require Import havm_interpreter.
From bpf.jit.havm Require Import HAVMState HAVMMonadOp DxHAVMInterpreter.

From bpf.jit.simulation Require Import MatchStateComm HAVMMatchState InterpreterRel.

(**
Check get_opcode.
get_opcode
     : nat -> M opcode

*)

Section Get_opcode_nat.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(nat:Type)].
  Definition res : Type := (opcode:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_opcode_nat.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_opcode_nat.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    (dcons (fun x => StateLess _ (opcode_correct x))
                (DList.DNil _)).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv hybrid_state := fun x  => StateLess _ (opcode_step_correct x).

  Instance correct_function_get_opcode_nat : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _op.

    unfold eval_inv, opcode_correct in c0.
    destruct c0 as (Hc_eq & Hc_range).
    subst.

    eexists. exists m, Events.E0.
    unfold byte_to_opcode.
    split_and; unfold step2; auto.
    -
      forward_star.
      simpl.
      rewrite Int.zero_ext_idem; [| lia].
      rewrite Int.zero_ext_and; [| lia].
      change (two_p 8 - 1)%Z with 255%Z.
      unfold Int.and.
      assert (Hc_z: (0 <= Z.of_nat c <= 255)%Z) by lia.
      rewrite Int.unsigned_repr with (z:=Z.of_nat c); [| change Int.max_unsigned with 4294967295%Z; lia].
      change (Int.unsigned (Int.repr 255)) with (Z.of_nat (Z.to_nat 255%Z)).
      change (Int.unsigned (Int.repr 7)) with (Z.of_nat (Z.to_nat 7%Z)).
      assert (Hzland: (0 <= Z.land (Z.of_nat c) (Z.of_nat (Z.to_nat 7)) <= 7)%Z). {
        split.
        rewrite Z.land_nonneg.
        right; lia.
        rewrite LemmaNat.land_land.
        change (Z.to_nat 7%Z) with 7%nat.
        assert (Hnat_land: (Nat.land c 7 <= 7)%nat) by (rewrite Nat.land_comm; rewrite LemmaNat.land_bound; lia).
        lia.
      }
      rewrite Int.unsigned_repr; [| change Int.max_unsigned with 4294967295%Z; lia].
      rewrite <- Z.land_assoc.
      simpl.
      forward_star.
    -
      unfold match_res, opcode_step_correct.
      assert (Hc_le: (0 <= Nat.land c 7 <= 7)%nat). {
        rewrite Nat.land_comm.
        split. lia.
        rewrite LemmaNat.land_bound.
        lia.
      }
      change 7%Z with (Z.of_nat (Z.to_nat 7%Z)).
      rewrite LemmaNat.land_land.
      change (Z.to_nat 7) with 7%nat.
      remember (Nat.land c 7) as n.
      destruct n eqn: Hld_imm.
      { exists 0%nat; split ;[ reflexivity | intuition]. }
      destruct n0 eqn: Hld_reg; [ reflexivity |].
      destruct n1 eqn: Hst_imm; [ reflexivity |].
      destruct n2 eqn: Hst_reg; [ reflexivity |].
      destruct n3 eqn: Halu32; [ reflexivity |].
      destruct n4 eqn: Hbranch; [ reflexivity |].
      exists n%nat; split ;[ subst n; reflexivity | intuition].
    - constructor.
      simpl.
      rewrite Int.zero_ext_and.
      change (two_p 8 - 1)%Z with 255%Z.
      unfold Int.and.
      change (Int.unsigned (Int.repr 255)) with (Z.of_nat (Z.to_nat 255%Z)).
      change 7%Z with (Z.of_nat (Z.to_nat 7%Z)) at 1.
      assert (Hzland: (0 <= Z.land (Z.of_nat c) (Z.of_nat (Z.to_nat 7)) <= 7)%Z). {
        split.
        rewrite Z.land_nonneg.
        right; lia.
        rewrite LemmaNat.land_land.
        change (Z.to_nat 7%Z) with 7%nat.
        assert (Hnat_land: (Nat.land c 7 <= 7)%nat) by (rewrite Nat.land_comm; rewrite LemmaNat.land_bound; lia).
        lia.
      }
      rewrite Int.unsigned_repr; [| change Int.max_unsigned with 4294967295%Z; lia].
      rewrite <- Z.land_assoc.
      simpl.
      reflexivity.
      lia.
    - apply unmodifies_effect_refl.
  Qed.

End Get_opcode_nat.

Existing Instance correct_function_get_opcode_nat.
