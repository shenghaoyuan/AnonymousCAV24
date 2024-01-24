From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma.

From bpf.jit.jitclight Require Import havm_interpreter.
From bpf.jit.havm Require Import HAVMState HAVMMonadOp.

From bpf.jit.simulation Require Import MatchStateComm HAVMMatchState InterpreterRel.


(**
Check upd_pc.
upd_pc
     : sint32_t -> M unit
 *)

Section Upd_pc.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(int:Type)].
  Definition res : Type := unit.

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := upd_pc.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_upd_pc.

  Definition modifies  := ModSomething. (* of the C code *)
  
  (* [match_arg] relates the Coq arguments and the C arguments *)
Definition match_arg_list : DList.t (fun (x:Type) => x -> Inv _) ((unit:Type) ::args) :=
    dcons  (fun (x:unit) => StateLess _ (is_state_handle))
                (dcons  (fun (x:int) => StateLess _ (uint32_correct x))
                             (DList.DNil _)).

(* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv hybrid_state := fun _  => StateLess _ (fun v => v = Vundef).

  Instance correct_function_upd_pc : forall a, correct_function _ p args res f fn modifies false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    repeat intro.

    simpl in c.
    unfold f; simpl.
    destruct upd_pc eqn: Hupd_pc; [| constructor].
    destruct p0.
    intros.
    unfold INV in H.
    get_invariant _st.
    get_invariant _pc.
    unfold eval_inv,is_state_handle in c0.
    unfold eval_inv, uint32_correct in c1.
    destruct c1 as (c1 & c1_range).
    subst.
    (** we need to get the proof of `upd_pc` store permission *)
    apply upd_pc_store with (pc:= (Int.add (pc_loc st) c)) in MS as Hstore.
    destruct Hstore as (m1 & Hstore).
    (** pc \in [ (state_block,0), (state_block,8) ) *)
    (**according to the type of upd_pc:
         static void upd_pc(struct bpf_state* st, unsigned long long pc)
       1. return value should be Vundef (i.e. void)
       2. the new memory should change the value of pc, i.e. m_pc
      *)
    exists Vundef, m1, Events.E0.

    split; unfold step2.
    - (* goal: Smallstep.star  _ _ (State _ (Ssequence ... *)
      destruct MS.
      unfold Mem.loadv in mpc.
      change (Ptrofs.unsigned (Ptrofs.repr 0)) with 0%Z in mpc.
      repeat forward_star.
      + rewrite Ptrofs.add_zero_l.
        unfold Ctypes.bitalignof; simpl.
        change (Ptrofs.unsigned (Ptrofs.repr (Coqlib.align 0 32 / 8))) with 0%Z.
        apply mpc.
      + 
        unfold Cop.sem_binary_operation, Cop.sem_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        f_equal.
      + unfold Cop.sem_cast; simpl.
        f_equal.

    - split_and.
      + reflexivity.
      + constructor.

      + unfold upd_pc in Hupd_pc.
        destruct Int.cmpu; inversion Hupd_pc.
        subst.
        eapply upd_pc_preserves_match_state; eauto.
      + constructor.
Qed.

End Upd_pc.

Existing Instance correct_function_upd_pc.
