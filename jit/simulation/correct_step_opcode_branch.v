From bpf.comm Require Import Flag Regs.
From bpf.monadicmodel Require Import Opcode.
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma CommonLib CommonLemmaNat.

From bpf.jit.simulation Require Import correct_get_opcode_branch correct_upd_pc
correct_upd_flag correct__bpf_get_call correct_cmp_ptr32_nullM correct_exec_function correct_upd_reg.

From bpf.jit.jitclight Require Import havm_interpreter.
From bpf.jit.havm Require Import HAVMState HAVMMonadOp DxHAVMInterpreter.

From bpf.jit.simulation Require Import MatchStateComm HAVMMatchState InterpreterRel.

(**
Check step_opcode_branch.
step_opcode_branch
     : val64_t ->
       val64_t -> DxIntegers.sint32_t -> DxIntegers.sint32_t -> nat8 -> M unit

*)
Open Scope Z_scope.

Section Step_opcode_branch.
  Context {S:special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val:Type); (val:Type); (int:Type); (nat:Type)].

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M unit) := step_opcode_branch.


  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_step_opcode_branch.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) ((unit:Type) ::args) :=
    (dcons (fun _ => StateLess _ is_state_handle)
      (dcons (stateless val32_correct)
       (dcons (stateless val32_correct)
          (dcons (stateless uint32_correct)
            (dcons (stateless opcode_correct)
                    (DList.DNil _)))))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv hybrid_state := fun _ => StateLess _ (eq Vundef).


  Lemma Cop_add : forall vl1 vl2 m,
       Cop.sem_binary_operation (globalenv p) Cop.Oadd
                                (Vint vl1) Ctypesdefs.tuint (Vint vl2) Ctypesdefs.tuint m =
         Some (Vint (Int.add vl1 vl2)).
  Proof.
    reflexivity.
  Qed.

  Instance correct_function_step_opcode_branch : forall a, correct_function _ p args res f fn modifies false match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.

    unfold f, step_opcode_branch.
    simpl. unfold bindM, returnM.
    (** goal: correct_body _ _ (bindM (get_opcode_branch _) ... *)
    correct_forward.

    get_invariant _op.
    exists (v::nil).
    split.
    unfold map_opt. unfold exec_expr. rewrite p0.
    reflexivity.
    intros. simpl.
    tauto.

    (** goal: correct_body _ _
              match x with
              | op_BPF_ADD64 => bindM (upd_reg ... *)
    intros.
    unfold INV.
    destruct x eqn: Hbranch. (**r case discussion on each branch_instruction *)
    - (**r op_BPF_JA *)
      eapply correct_statement_switch with (n:= 0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward.
        correct_forward.

        get_invariant _st.
        get_invariant _ofs.
        unfold eval_inv,uint32_correct,stateless in c4.
        destruct c4 as (c4 & c4_range).
        subst.
        exists (v :: Vint c1 :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1.
        split.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add,
          Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless, uint32_correct.
        split; [reflexivity | apply Int.unsigned_range_2].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.
        correct_forward.

        get_invariant _st.
        unfold eval_inv, is_state_handle in c3.
        exists (v ::Vint (Int.repr 2) :: nil).
        unfold map_opt, exec_expr.
        rewrite p0.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,flag_correct.
        unfold int_of_flag; simpl. reflexivity.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.

        get_invariant _op.
        unfold exec_expr.
        rewrite p0. simpl.
        unfold stateless, opcode_correct in c3.
        destruct c3 as (Hv_eq & Hrange).
        rewrite <- Hv_eq.
        destruct (c2 =? 5)%nat eqn: Hc2_eq.
        rewrite Nat.eqb_eq in Hc2_eq.
        subst.
        simpl.
        reflexivity.

        rewrite Nat.eqb_neq in Hc2_eq.
        simpl.
        unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
        unfold Cop.sem_cast; simpl.
        assert (Hneq: Int.eq (Int.repr (Z.of_nat c2)) (Int.repr 5) = false). {
          apply Int.eq_false.
          apply nat8_neq_k; auto; lia.
        }
        rewrite Hneq; clear Hneq. unfold DxNat.nat8_0x05. simpl. unfold Val.of_bool.
rewrite <- Nat.eqb_neq in Hc2_eq.
        rewrite Hc2_eq.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c3.
        unfold opcode_branch_correct in c3.
        change (Int.repr (Z.of_nat (Nat.land 5 240))) with (Int.repr 0) in c3.
        assumption.
      + compute. intuition congruence.

    - (**r op_BPF_JEQ *)
      eapply correct_statement_switch with (n:= 0x10).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.comp_eq.
        correct_forward.
        correct_forward.

        get_invariant _st.
        get_invariant _ofs.
        unfold eval_inv in *.
        unfold eval_inv,uint32_correct,stateless in c4.
        destruct c4 as (c4 & c4_range).
        subst.
        exists (v :: Vint c1 :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add,
          Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,uint32_correct.
        split; [reflexivity | apply Int.unsigned_range_2].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.

        get_invariant _dst32.
        get_invariant _src32.
        unfold stateless, val32_correct in c3.
        destruct c3 as (c3_eq & (c3_vl & c3)).
        unfold stateless, val32_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c3.
        unfold opcode_branch_correct in c3.
        change (Int.repr (Z.of_nat (Nat.land 21 240))) with (Int.repr 0x10) in c3.
        change (Int.repr (Z.of_nat (Nat.land 29 240))) with (Int.repr 0x10) in c3.
        destruct c3; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JGT *)
      eapply correct_statement_switch with (n:= 0x20).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compu_gt.
        correct_forward.
        correct_forward.

        get_invariant _st.
        get_invariant _ofs.
        unfold eval_inv in *.
        unfold eval_inv,uint32_correct,stateless in c4.
        destruct c4 as (c4 & c4_range).
        subst.
        exists (v :: Vint c1 :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add,
          Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,uint32_correct.
        split; [reflexivity | apply Int.unsigned_range_2].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.

        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.

        intros.
        get_invariant _dst32.
        get_invariant _src32.
        unfold stateless, val32_correct in c3.
        destruct c3 as (c3_eq & (c3_vl & c3)).
        unfold stateless, val32_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c3.
        unfold opcode_branch_correct in c3.
        change (Int.repr (Z.of_nat (Nat.land 37 240))) with (Int.repr 0x20) in c3.
        change (Int.repr (Z.of_nat (Nat.land 45 240))) with (Int.repr 0x20) in c3.
        destruct c3; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JGE *)
      eapply correct_statement_switch with (n:= 0x30).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compu_ge.
        correct_forward.
        correct_forward.

        get_invariant _st.
        get_invariant _ofs.
        unfold eval_inv in *.
        unfold uint32_correct,stateless in c4.
        destruct c4 as (c4 & c4_range).
        subst.
        exists (v :: Vint c1 :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add,
          Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,uint32_correct.
        split; [reflexivity | apply Int.unsigned_range_2].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.

        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.
        intros.
        get_invariant _dst32.
        get_invariant _src32.
        unfold stateless, val32_correct in c3.
        destruct c3 as (c3_eq & (c3_vl & c3)).
        unfold stateless, val32_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c3.
        unfold opcode_branch_correct in c3.
        change (Int.repr (Z.of_nat (Nat.land 53 240))) with (Int.repr 0x30) in c3.
        change (Int.repr (Z.of_nat (Nat.land 61 240))) with (Int.repr 0x30) in c3.
        destruct c3; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JLT *)
      eapply correct_statement_switch with (n:= 0xa0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compu_lt.
        correct_forward.
        correct_forward.

        get_invariant _st.
        get_invariant _ofs.
        unfold eval_inv in *.
        unfold uint32_correct,stateless in c4.
        destruct c4 as (c4 & c4_range).
        subst.
        exists (v :: Vint c1 :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add,
          Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,uint32_correct.
        split; [reflexivity | apply Int.unsigned_range_2].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.

        intros.
        get_invariant _dst32.
        get_invariant _src32.
        unfold stateless, val32_correct in c3.
        destruct c3 as (c3_eq & (c3_vl & c3)).
        unfold stateless, val32_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c3.
        unfold opcode_branch_correct in c3.
        change (Int.repr (Z.of_nat (Nat.land 165 240))) with (Int.repr 0xa0) in c3.
        change (Int.repr (Z.of_nat (Nat.land 173 240))) with (Int.repr 0xa0) in c3.
        destruct c3; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JLE *)
      eapply correct_statement_switch with (n:= 0xb0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compu_le.
        correct_forward.
        correct_forward.

        get_invariant _st.
        get_invariant _ofs.
        unfold eval_inv in *.
        unfold uint32_correct,stateless in c4.
        destruct c4 as (c4 & c4_range).
        subst.
        exists (v :: Vint c1 :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add,
          Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,uint32_correct.
        split; [reflexivity | apply Int.unsigned_range_2].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.

        intros.
        get_invariant _dst32.
        get_invariant _src32.
        unfold stateless, val32_correct in c3.
        destruct c3 as (c3_eq & (c3_vl & c3)).
        unfold stateless, val32_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c3.
        unfold opcode_branch_correct in c3.
        change (Int.repr (Z.of_nat (Nat.land 181 240))) with (Int.repr 0xb0) in c3.
        change (Int.repr (Z.of_nat (Nat.land 189 240))) with (Int.repr 0xb0) in c3.
        destruct c3; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JSET *)
      eapply correct_statement_switch with (n:= 0x40).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.compu_set.
        correct_forward.
        correct_forward.

        get_invariant _st.
        get_invariant _ofs.
        unfold eval_inv in *.
        unfold uint32_correct,stateless in c4.
        destruct c4 as (c4 & c4_range).
        subst.
        exists (v :: Vint c1 :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add,
          Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,uint32_correct.
        split; [reflexivity | apply Int.unsigned_range_2].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.

        intros.
        get_invariant _dst32.
        get_invariant _src32.
        unfold stateless, val32_correct in c3.
        destruct c3 as (c3_eq & (c3_vl & c3)).
        unfold stateless, val32_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c3.
        unfold opcode_branch_correct in c3.
        change (Int.repr (Z.of_nat (Nat.land 69 240))) with (Int.repr 0x40) in c3.
        change (Int.repr (Z.of_nat (Nat.land 77 240))) with (Int.repr 0x40) in c3.
        destruct c3; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JNE *)
      eapply correct_statement_switch with (n:= 0x50).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.comp_ne.
        correct_forward.
        correct_forward.

        get_invariant _st.
        get_invariant _ofs.
        unfold eval_inv in *.
        unfold uint32_correct,stateless in c4.
        destruct c4 as (c4 & c4_range).
        subst.
        exists (v :: Vint c1 :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add,
          Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,uint32_correct.
        split; [reflexivity | apply Int.unsigned_range_2].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.

        intros.
        get_invariant _dst32.
        get_invariant _src32.
        unfold stateless, val32_correct in c3.
        destruct c3 as (c3_eq & (c3_vl & c3)).
        unfold stateless, val32_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c3.
        unfold opcode_branch_correct in c3.
        change (Int.repr (Z.of_nat (Nat.land 85 240))) with (Int.repr 0x50) in c3.
        change (Int.repr (Z.of_nat (Nat.land 93 240))) with (Int.repr 0x50) in c3.
        destruct c3; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JSGT *)
      eapply correct_statement_switch with (n:= 0x60).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.comp_gt.
        correct_forward.
        correct_forward.

        get_invariant _st.
        get_invariant _ofs.
        unfold eval_inv in *.
        unfold uint32_correct,stateless in c4.
        destruct c4 as (c4 & c4_range).
        subst.
        exists (v :: Vint c1 :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add,
          Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,uint32_correct.
        split; [reflexivity | apply Int.unsigned_range_2].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.

        intros.
        get_invariant _dst32.
        get_invariant _src32.
        unfold stateless, val32_correct in c3.
        destruct c3 as (c3_eq & (c3_vl & c3)).
        unfold stateless, val32_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c3.
        unfold opcode_branch_correct in c3.
        change (Int.repr (Z.of_nat (Nat.land 101 240))) with (Int.repr 0x60) in c3.
        change (Int.repr (Z.of_nat (Nat.land 109 240))) with (Int.repr 0x60) in c3.
        destruct c3; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JSGE *)
      eapply correct_statement_switch with (n:= 0x70).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.comp_ge.
        correct_forward.
        correct_forward.

        get_invariant _st.
        get_invariant _ofs.
        unfold eval_inv in *.
        unfold uint32_correct,stateless in c4.
        destruct c4 as (c4 & c4_range).
        subst.
        exists (v :: Vint c1 :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add,
          Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,uint32_correct.
        split; [reflexivity | apply Int.unsigned_range_2].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.

        intros.
        get_invariant _dst32.
        get_invariant _src32.
        unfold stateless, val32_correct in c3.
        destruct c3 as (c3_eq & (c3_vl & c3)).
        unfold stateless, val32_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c3.
        unfold opcode_branch_correct in c3.
        change (Int.repr (Z.of_nat (Nat.land 117 240))) with (Int.repr 0x70) in c3.
        change (Int.repr (Z.of_nat (Nat.land 125 240))) with (Int.repr 0x70) in c3.
        destruct c3; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JSLT *)
      eapply correct_statement_switch with (n:= 0xc0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.comp_lt.
        correct_forward.
        correct_forward.

        get_invariant _st.
        get_invariant _ofs.
        unfold eval_inv in *.
        unfold uint32_correct,stateless in c4.
        destruct c4 as (c4 & c4_range).
        subst.
        exists (v :: Vint c1 :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add,
          Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,uint32_correct.
        split; [reflexivity | apply Int.unsigned_range_2].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.

        intros.
        get_invariant _dst32.
        get_invariant _src32.
        unfold stateless, val32_correct in c3.
        destruct c3 as (c3_eq & (c3_vl & c3)).
        unfold stateless, val32_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c3.
        unfold opcode_branch_correct in c3.
        change (Int.repr (Z.of_nat (Nat.land 197 240))) with (Int.repr 0xc0) in c3.
        change (Int.repr (Z.of_nat (Nat.land 205 240))) with (Int.repr 0xc0) in c3.
        destruct c3; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_JSLE *)
      eapply correct_statement_switch with (n:= 0xd0).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        unfold rBPFValues.comp_le.
        correct_forward.
        correct_forward.

        get_invariant _st.
        get_invariant _ofs.
        unfold eval_inv in *.
        unfold uint32_correct,stateless in c4.
        destruct c4 as (c4 & c4_range).
        subst.
        exists (v :: Vint c1 :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1.
        split.
        subst.
        unfold Cop.sem_unary_operation, Cop.sem_binary_operation, Cop.sem_add,
          Cop.classify_add, Cop.sem_binarith, Cop.sem_cast; simpl.
        reflexivity.
        intros.
        simpl.
        intuition.
        unfold stateless,uint32_correct.
        split; [reflexivity | apply Int.unsigned_range_2].
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.

        intros.
        get_invariant _dst32.
        get_invariant _src32.
        unfold stateless, val32_correct in c3.
        destruct c3 as (c3_eq & (c3_vl & c3)).
        unfold stateless, val32_correct in c4.
        destruct c4 as (c4_eq & (c4_vl & c4)).
        subst.
        unfold exec_expr.
        rewrite p0,p1.
        simpl.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c3.
        unfold opcode_branch_correct in c3.
        change (Int.repr (Z.of_nat (Nat.land 213 240))) with (Int.repr 0xd0) in c3.
        change (Int.repr (Z.of_nat (Nat.land 221 240))) with (Int.repr 0xd0) in c3.
        destruct c3; intuition.
      + compute. intuition congruence.
    - (**r op_BPF_CALL *)
      eapply correct_statement_switch with (n:= 0x80).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward.
        correct_forward.

        get_invariant _src32.
        unfold val64_correct,stateless in c3.
        destruct c3 as (Hv_eq & vl & Hvl_eq); subst.
        exists ((Vint vl) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        simpl.
        split; [reflexivity |].
        intros.
        unfold stateless, val32_correct, DxValues.uvint_to_svint.
        intuition eauto.
        intros.

        correct_forward.

        get_invariant _f_ptr.
        unfold eval_inv,correct__bpf_get_call.match_res, val_ptr_correct in c3.
        subst.
        unfold correct_cmp_ptr32_nullM.match_arg_list.
        exists (v :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        simpl.
        split; [reflexivity |].
        get_invariant _f_ptr. unfold eval_inv in c3.
        unfold correct__bpf_get_call.match_res  in c3.
        intros.
        unfold val_ptr_correct.
        intuition congruence.
        intros.


        correct_forward.

        change (upd_flag Flag.BPF_ILLEGAL_CALL) with
          (bindM (upd_flag Flag.BPF_ILLEGAL_CALL) (fun _ : unit => returnM tt)).
        unfold bindM, returnM.
        correct_forward.
 simpl in H.
        get_invariant _st.
        exists (v ::Vint (Int.repr 5) :: nil).
        unfold map_opt, exec_expr.
        rewrite p0.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        unfold stateless,flag_correct.
        intuition congruence.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.

        correct_forward.
 simpl in H.
        get_invariant _st.
        get_invariant _f_ptr.
        unfold eval_inv, is_state_handle in c4.
        unfold eval_inv,correct__bpf_get_call.match_res, val_ptr_correct in c4.
        unfold correct_exec_function.match_arg_list.
        exists (v :: v0 :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1.
        simpl.
        split; [reflexivity |].
        intros.
        intuition congruence.
        intros.

        assert (Heq: (upd_reg R0 x2) =
          (bindM (upd_reg R0 x2) (fun _ : unit => returnM tt))). {
          unfold bindM, returnM.
          unfold upd_reg.
          destruct x2; reflexivity.
        }
        rewrite Heq; clear Heq.
        unfold bindM, returnM.

        correct_forward.
 simpl in H.
        get_invariant _st.
        get_invariant _res.
        unfold eval_inv, is_state_handle in c4.
        unfold eval_inv,correct_exec_function.match_res, val32_correct in c4.
        destruct c4 as (Hv0_eq & vi & Hvi_eq); subst.
        exists (v :: (Vint (Int.repr 0)) :: (Vint vi) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0, p1.
        simpl.
        split; [reflexivity |].
        intros.
        unfold stateless, reg_correct, val32_correct.
        intuition eauto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res.
        reflexivity.

        get_invariant _is_null.
        unfold exec_expr, Val.of_bool.
        rewrite p0.
        unfold correct_cmp_ptr32_nullM.match_res, match_bool in c3.
        rewrite c3.
        unfold Vtrue, Vfalse.
        destruct x1; reflexivity.

        correct_forward.

        get_invariant _st.
        unfold eval_inv, is_state_handle in c3.
        exists (v :: (Vint (Int.repr 2)) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        simpl.
        split; [reflexivity |].
        intros.
        unfold stateless, flag_correct, int_of_flag; simpl.
        intuition eauto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.

        get_invariant _op.
        unfold exec_expr.
        rewrite p0. simpl.
        unfold stateless, opcode_correct in c3.
        destruct c3 as (Hv_eq & Hrange).
        rewrite <- Hv_eq.
        destruct (c2 =? 133)%nat eqn: Hc2_eq.
        rewrite Nat.eqb_eq in Hc2_eq.
        subst.
        simpl.
        reflexivity.

        rewrite Nat.eqb_neq in Hc2_eq.
        simpl.
        unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
        unfold Cop.sem_cast; simpl.
        assert (Hneq: Int.eq (Int.repr (Z.of_nat c2)) (Int.repr 133) = false). {
          apply Int.eq_false.
          apply nat8_neq_k; auto; lia.
        }
        rewrite Hneq; clear Hneq.
        unfold DxNat.nat8_0x85.
        rewrite <- Nat.eqb_neq in Hc2_eq.
        rewrite Hc2_eq.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c3.
        unfold opcode_branch_correct in c3.
        change (Int.repr (Z.of_nat (Nat.land 133 240))) with (Int.repr 0x80) in c3.
        assumption.
      + compute. intuition congruence.
    - (**r op_BPF_RET *)
      eapply correct_statement_switch with (n:= 0x90).
      + simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.
        correct_forward.
        correct_forward.

        get_invariant _st.
        get_invariant _ofs.
        unfold eval_inv in *.
        unfold uint32_correct,stateless in c4.
        destruct c4 as (c4 & c4_range).
        subst.
        exists (v :: Vint (Int.repr 1) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split. reflexivity.
        subst.
        intros.
        simpl.
        intuition.
        unfold stateless,flag_correct, int_of_flag.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.
        correct_forward.

        get_invariant _st.
        exists (v ::Vint (Int.repr 2) :: nil).
        unfold map_opt, exec_expr.
        rewrite p0.
        split.
        simpl.
        reflexivity.
        intros.
        simpl.
        unfold stateless,flag_correct.
        intuition.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.

        intros.
        get_invariant _op.
        unfold exec_expr.
        rewrite p0. simpl.
        unfold stateless, opcode_correct in c3.
        destruct c3 as (Hv_eq & Hrange).
        rewrite <- Hv_eq.
        destruct (c2 =? 149)%nat eqn: Hc2_eq.
        rewrite Nat.eqb_eq in Hc2_eq.
        subst.
        simpl.
        reflexivity.

        rewrite Nat.eqb_neq in Hc2_eq.
        simpl.
        unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
        unfold Cop.sem_cast; simpl.
        assert (Hneq: Int.eq (Int.repr (Z.of_nat c2)) (Int.repr 149) = false). {
          apply Int.eq_false.
          apply nat8_neq_k; auto; lia.
        }
        rewrite Hneq; clear Hneq.
        unfold DxNat.nat8_0x95.
        rewrite <- Nat.eqb_neq in Hc2_eq.
        rewrite Hc2_eq.
        reflexivity.
      + reflexivity.
      + intros.
        get_invariant _opcode_jmp.
        unfold exec_expr.
        rewrite p0. f_equal.
        unfold correct_get_opcode_branch.match_res in c3.
        unfold opcode_branch_correct in c3.
        change (Int.repr (Z.of_nat (Nat.land 149 240))) with (Int.repr 0x90) in c3.
        destruct c3; intuition.
      + compute. intuition congruence.

    - (**r op_BPF_JMP_ILLEGAL_INS *)
      eapply correct_statement_switch_ex.
      + reflexivity.
      + intros.
        assert (Hillegal_ins: exists n i,
          eval_inv (correct_get_opcode_branch.match_res op_BPF_JMP_ILLEGAL_INS) n st0 m0 /\
          n = Vint (Int.repr (Z.of_nat (Nat.land i 240))) /\
          is_illegal_jmp_ins i /\
          exec_expr (Smallstep.globalenv (semantics2 p)) empty_env le0 m0
            (Etempvar _opcode_jmp Ctypesdefs.tuchar) =
              Some (Vint (Int.repr (Z.of_nat (Nat.land i 240))))).
        {
          get_invariant _opcode_jmp.
          unfold correct_get_opcode_branch.match_res in c3.
          exists v.
          assert (c4':=c3).
          unfold opcode_branch_correct in c4'.
          destruct c4' as (i & V & ILL).
          exists i.
          split ; auto.
          split ; auto.
          split ; auto.
          unfold exec_expr. congruence.
        }
        destruct Hillegal_ins as (n & i & Hprop & Hn_eq & Hill & EX).
        exists (Z.of_nat (Nat.land i 240)).
        split; auto.
        split.

        change Int.modulus with 4294967296.
        assert (Hand_le: (Nat.land 240 i <= 240)%nat). {
          apply LemmaNat.land_bound.
        }
        rewrite Nat.land_comm.
        lia.

        unfold select_switch.
        unfold select_switch_case.
        unfold is_illegal_jmp_ins in Hill.
        repeat match goal with
        | |- context[Coqlib.zeq ?x (Z.of_nat (Nat.land i 240))] =>
            destruct (Coqlib.zeq x (Z.of_nat (Nat.land i 240))) ; try lia
        end.
        (* default *)
        simpl.
        (**r s1 -> (Ssequence s1 s2) *)
        eapply correct_statement_seq_body_drop.
        intros.

        correct_forward.

        get_invariant _st.
        get_invariant _ofs.
        unfold eval_inv in *.
        unfold uint32_correct,stateless in c4.
        destruct c4 as (c4 & c4_range).
        subst.
        exists (v :: Vint (Int.repr 2) :: nil). (**r star here *)
        unfold map_opt, exec_expr.
        rewrite p0.
        split. reflexivity.
        subst.
        intros.
        simpl.
        unfold stateless,flag_correct, int_of_flag; simpl.
        split; auto.
        intros.

        (**r goal: correct_body p unit (returnM tt) fn (Sreturn None) modifies *)
        correct_forward.
        unfold match_res, correct_get_opcode_branch.match_res.
        reflexivity.
Qed.

End Step_opcode_branch.

Close Scope Z_scope.

Existing Instance correct_function_step_opcode_branch.
