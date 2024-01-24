From bpf.comm Require Import LemmaInt Regs JITCall.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory Memdata.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma CommonLib.

From bpf.jit.jitclight Require Import havm_interpreter.
From bpf.jit Require Import KeyValue2.
From bpf.jit.havm Require Import HAVMState HAVMMonadOp.

From bpf.jit.simulation Require Import MatchStateComm HAVMMatchState InterpreterRel.


Section Jit_call.
  Context {S : special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := jit_call.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_jit_call.

  Definition modifies  := ModSomething. (* of the C code *)

  (* [match_arg] relates the Coq arguments and the C arguments *)


Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    dcons (fun x => StateLess _ (is_state_handle)) (DList.DNil _).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv hybrid_state := fun _  => StateLess _ (fun v => v = Vundef).

  Instance correct_function_upd_reg : forall a, correct_function _ p args res f fn modifies false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.
    unfold INV in H.
    get_invariant _st.
    unfold eval_inv,is_state_handle in c.
    unfold f, jit_call.
    unfold HAVMState.jit_call.
    destruct ListKeyV.index eqn: Hnth; [| auto].
    destruct jit_call_simpl as [((pc1 & rs1) & m1) |] eqn: Hcall; [| auto].
    intros.
    exists Vundef, m1, Events.E0.

    unfold jit_call_simpl in Hcall.
    destruct Mem.alloc as (m2 & st_blk2) eqn: Halloc.
    destruct rbpf_copy_to as [m3 |] eqn: Hcopy_to; [| inversion Hcall].
    destruct ABinSem.bin_exec as [(res & m4)|] eqn: Hbin; [| inversion Hcall].
    destruct rbpf_copy_from as [(pc2 & rs2)|] eqn: Hcopy_from; [| inversion Hcall].
    destruct pc2; inversion Hcall; subst; clear Hcall.

    unfold state_block_size in Halloc.
    split.
    { admit.
    }

    split_and.
    - unfold eval_inv, match_res; simpl.
      reflexivity.
    - constructor.
    - unfold upd_regs, upd_mem, HAVMState.upd_pc; simpl.
      inversion MS.
      split; simpl.
      + eapply Mem.unchanged_on_refl; eauto.
      + 
    - simpl; auto.
Qed.

End Upd_reg.

Existing Instance correct_function_upd_reg.
