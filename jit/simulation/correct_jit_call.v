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

(*

Axiom bin_exec_mem_inv1:
  forall fuel sg sz ofs lv m1 m2 res,
    ABinSem.bin_exec fuel sg sz ofs lv m1 = Some (res, m2) -> m1 = m2.

Axiom bin_exec_mem_inv2:
  forall fuel sg sz ofs lv m1 m2 m1' res P,
    ABinSem.bin_exec fuel sg sz ofs lv m1 = Some (res, m1') ->
    Mem.unchanged_on P m1 m2 ->
    exists m2',
    ABinSem.bin_exec fuel sg sz ofs lv m2 = Some (res, m2') /\
    Mem.unchanged_on P m1' m2'. *)

Axiom bin_exec_mem_inv:
  forall fuel sg sz ofs lv m m3 m4 res st pc1 rs1
    (MS : match_state st m)
    (Hcopy_to : rbpf_copy_to (pc_loc st) (regs_st st) jit_state_block (bpf_m st) = Some m3)
    (Hbin : ABinSem.bin_exec fuel sg sz ofs lv m3 = Some (res, m4))
    (Hcopy_from : rbpf_copy_from (regs_st st) jit_state_block m4 = Some (Vint pc1, rs1)),
      exists m',
        ABinSem.bin_exec fuel sg sz ofs lv m = Some (res, m') /\
        match_state (upd_mem (bpf_m st) (upd_regs rs1 (HAVMState.upd_pc pc1 st))) m'.


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

    unfold jit_call_simpl in Hcall.
    destruct rbpf_copy_to as [m3 |] eqn: Hcopy_to; [| inversion Hcall].
    destruct ABinSem.bin_exec as [(res & m4)|] eqn: Hbin; [| inversion Hcall].
    destruct rbpf_copy_from as [(pc2 & rs2)|] eqn: Hcopy_from; [| inversion Hcall].
    destruct pc2; inversion Hcall; subst; clear Hcall.

    set (HST := MS).
    destruct HST.
    simpl in mpc.
    simpl in mkv.
    destruct mkv as (Hload_kv & Hkv).
    unfold match_kv in Hkv.
    destruct Hkv as (Hkv_len & Hkv_max & Hkv).
    unfold match_list_kv in Hkv.
    destruct mbin as (Hload_bin & mbin & Heq1 & Heq2).
    eapply bin_exec_mem_inv in Hbin as Hm_eq; eauto.
    destruct Hm_eq as (m' & Hbin1 & Hst1).

    assert (Hmem_unchanged_on_m3_m: Mem.unchanged_on (fun b _ =>
               b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk /\ b <> jit_blk /\ b <> kv_blk) m3 m). {
      eapply rbpf_copy_to_unchanged_on with (m := m) in Hcopy_to; eauto.
      intros ofs HF.
      destruct HF as (HF & _).
      apply HF.
      auto.
    }

    unfold ListKeyV.index in Hnth.
    specialize (Hkv (Z.to_nat (Int.unsigned (pc_loc st)))).
    assert (Hr: (0 <= Z.to_nat (Int.unsigned (pc_loc st)) < length (tp_kv st))%nat).
    {
      clear - Hnth.
      split; [lia | ].
      eapply nth_error_Some; eauto.
      intro HF.
      rewrite HF in Hnth.
      inversion Hnth.
    }
    specialize (Hkv Hr).
    destruct Hkv as (Hkv1 & Hkv2).
    unfold Mem.loadv in Hkv1.
    assert (Heq:
    (Ptrofs.unsigned (Ptrofs.repr (8 * Z.of_nat (Z.to_nat (Int.unsigned (pc_loc st)))))) =
    (Ptrofs.unsigned (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_intu (pc_loc st))))). {
      clear - Hr.
      f_equal.
      unfold Ptrofs.mul, Ptrofs.of_intu, Ptrofs.of_int.
      f_equal.
      change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8%Z.
      rewrite Ptrofs.unsigned_repr_eq.
      change Ptrofs.modulus with Int.modulus.
      rewrite <- Int.unsigned_repr_eq.
      rewrite Int.repr_unsigned.
      rewrite Z2Nat.id.
      f_equal.
      set (Int_unsigned_ge_zero (pc_loc st)) as Heq. lia.
    }
    rewrite Heq in Hkv1; clear Heq.

    unfold Mem.loadv in Hkv2.
    assert (Heq: (Ptrofs.unsigned (Ptrofs.repr (8 * Z.of_nat (Z.to_nat (Int.unsigned (pc_loc st))) + 4))) = (Ptrofs.unsigned
(Ptrofs.add (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_intu (pc_loc st))) (Ptrofs.repr 4)))). {
      clear - Hr Hkv_len Hkv_max.
      f_equal.
      unfold Ptrofs.add, Ptrofs.mul, Ptrofs.of_intu, Ptrofs.of_int.
      f_equal.
      change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8%Z.
      change (Ptrofs.unsigned (Ptrofs.repr 4)) with 4%Z.
      repeat rewrite Ptrofs.unsigned_repr_eq.
      change Ptrofs.modulus with Int.modulus.
      repeat rewrite <- Int.unsigned_repr_eq.
      set (Int_unsigned_ge_zero (pc_loc st)) as Heq.
      rewrite Int.repr_unsigned.
      rewrite Z2Nat.id; try lia.
      rewrite Int.unsigned_repr.
      - f_equal.
      - change Int.max_unsigned with Ptrofs.max_unsigned.
          rewrite Hkv_len in *.
          change  Ptrofs.max_unsigned with 4294967295%Z in *.
          split; lia.
    }
    rewrite Heq in Hkv2; clear Heq.
(*
    assert (Hstore_m:
      exists mk, Mem.store AST.Mint32 m st_blk (Ptrofs.unsigned (Ptrofs.repr 44))
  (Vint (Int.add (pc_loc st) (Int.repr (Z.of_nat (alu32_ofs k))))) = Some mk). {
      assert (Heq: Mem.valid_access m AST.Mint32 st_blk
        (Ptrofs.unsigned (Ptrofs.repr 44)) Writable). {
        destruct mperm as (Hrange & _).
        clear- Hrange.
        eapply Mem.valid_access_freeable_any; eauto.
        unfold Mem.valid_access.
        change (Ptrofs.unsigned (Ptrofs.repr 44)) with 44%Z in *.
        simpl.
        split.
        - unfold Mem.range_perm in *.
          intros.
          apply Hrange.
          lia.
        - change 44%Z with (4 * 11)%Z.
          apply Z.divide_factor_l.
      }
      eapply Mem.valid_access_store in Heq.
      destruct Heq as (mk & Heq).
      exists mk.
      rewrite Heq; auto.
    }
    destruct Hstore_m as (mk & Hstore_m). *)
    exists Vundef, m', Events.E0.

    unfold stack_block_size in Hbin.
    split.
    { eapply Smallstep.star_step with (t1 := Events.E0) (t2 := Events.E0); eauto.
      { eapply step_seq. }
      eapply Smallstep.star_step with (t1 := Events.E0) (t2 := Events.E0); eauto.
      { eapply step_set; forward_expr.
        - rewrite Ptrofs.add_zero_l.
          unfold Coqlib.align; simpl.
          change (Ptrofs.unsigned (Ptrofs.repr (544 / 8))) with
            (Ptrofs.unsigned (Ptrofs.repr 68)).
          rewrite Hload_kv.
          reflexivity.
        - rewrite Ptrofs.add_zero_l.
          unfold Coqlib.align; simpl.
          change (Ptrofs.unsigned (Ptrofs.repr (352 / 8))) with
            (Ptrofs.unsigned (Ptrofs.repr 44)).
          rewrite mpc.
          reflexivity.
        - unfold Cop.sem_binary_operation, Cop.sem_add; simpl.
          fold Ptrofs.zero.
          rewrite Ptrofs.add_zero_l.
          unfold Coqlib.align; simpl.
          reflexivity.
        - unfold Coqlib.align; simpl.
          change (0 / 8)%Z with 0%Z.
          fold Ptrofs.zero.
          rewrite Ptrofs.add_zero.
          rewrite Hkv1.
          eapply nth_error_nth with (d := empty_kv) in Hnth.
          rewrite Hnth.
          reflexivity.
      }

      eapply Smallstep.star_step with (t1 := Events.E0) (t2 := Events.E0); eauto.
      { eapply step_skip_seq. }

      eapply Smallstep.star_step with (t1 := Events.E0) (t2 := Events.E0); eauto.
      { eapply step_seq. }

      eapply Smallstep.star_step with (t1 := Events.E0) (t2 := Events.E0); eauto.
      { eapply step_builtin.
        - econstructor; eauto.
          { forward_expr.
            * rewrite Maps.PTree.gso; [ | intro HF; inversion HF].
              rewrite p0.
              reflexivity.
            * rewrite Ptrofs.add_zero_l.
              unfold Coqlib.align; simpl.
              change (Ptrofs.unsigned (Ptrofs.repr (608 / 8))) with
                (Ptrofs.unsigned (Ptrofs.repr 76)).
              simpl in Hload_bin.
              rewrite Hload_bin.
              reflexivity.
            * rewrite Maps.PTree.gss.
              reflexivity.
            * unfold Cop.sem_binary_operation, Cop.sem_add; simpl.
              fold Ptrofs.zero.
              rewrite Ptrofs.add_zero_l.
              reflexivity.
          }
          { unfold Cop.sem_cast; simpl.
            reflexivity. }

          econstructor; eauto.
          { forward_expr.
            rewrite Maps.PTree.gso; [ | intro HF; inversion HF].
            rewrite p0.
            reflexivity.
          }
          { unfold Cop.sem_cast; simpl.
            reflexivity. }

          econstructor; eauto.
        - unfold Events.external_call; simpl.
          split; [reflexivity|].
          unfold JITTED_LIST_MAX_LENGTH, compcertbin_signature,
            AST.cc_default, stack_block_size in Hbin1.
          change (Int.unsigned (Int.repr 48)) with 48%Z in Hbin1.
          fold Ptrofs.zero.
          rewrite Heq1, Heq2 in Hbin1.
          change (Pos.to_nat 4000) with 4000%nat.
          rewrite Hbin1.
          reflexivity.
      }

      eapply Smallstep.star_step with (t1 := Events.E0) (t2 := Events.E0); eauto.
      { eapply step_skip_seq. }

      eapply Smallstep.star_step with (t1 := Events.E0) (t2 := Events.E0); eauto.
      { eapply step_seq. }

      clear - Hnth p0 Hst1.
      destruct Hst1.


    simpl in mpc.
    simpl in mkv.
    destruct mkv as (Hload_kv & Hkv).
    unfold match_kv in Hkv.
    destruct Hkv as (Hkv_len & Hkv_max & Hkv).
    unfold match_list_kv in Hkv.
    destruct mbin as (Hload_bin & mbin & Heq1 & Heq2).

    unfold ListKeyV.index in Hnth.
    specialize (Hkv (Z.to_nat (Int.unsigned ((Int.add (pc_loc st) pc1))))).
    assert (Hr: (0 <= Z.to_nat (Int.unsigned ((Int.add (pc_loc st) pc1))) < length (tp_kv st))%nat).
    {
      clear - Hnth.
      split; [lia | ].
      eapply nth_error_Some; eauto.
      intro HF.
      rewrite HF in Hnth.
      inversion Hnth.
    }
    specialize (Hkv Hr).
    destruct Hkv as (Hkv1 & Hkv2).
    unfold Mem.loadv in Hkv1.
    assert (Heq:
    (Ptrofs.unsigned (Ptrofs.repr (8 * Z.of_nat (Z.to_nat (Int.unsigned (pc_loc st)))))) =
    (Ptrofs.unsigned (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_intu (pc_loc st))))). {
      clear - Hr.
      f_equal.
      unfold Ptrofs.mul, Ptrofs.of_intu, Ptrofs.of_int.
      f_equal.
      change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8%Z.
      rewrite Ptrofs.unsigned_repr_eq.
      change Ptrofs.modulus with Int.modulus.
      rewrite <- Int.unsigned_repr_eq.
      rewrite Int.repr_unsigned.
      rewrite Z2Nat.id.
      f_equal.
      set (Int_unsigned_ge_zero (pc_loc st)) as Heq. lia.
    }
    rewrite Heq in Hkv1; clear Heq.

    unfold Mem.loadv in Hkv2.
    assert (Heq: (Ptrofs.unsigned (Ptrofs.repr (8 * Z.of_nat (Z.to_nat (Int.unsigned (pc_loc st))) + 4))) = (Ptrofs.unsigned
(Ptrofs.add (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_intu (pc_loc st))) (Ptrofs.repr 4)))). {
      clear - Hr Hkv_len Hkv_max.
      f_equal.
      unfold Ptrofs.add, Ptrofs.mul, Ptrofs.of_intu, Ptrofs.of_int.
      f_equal.
      change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8%Z.
      change (Ptrofs.unsigned (Ptrofs.repr 4)) with 4%Z.
      repeat rewrite Ptrofs.unsigned_repr_eq.
      change Ptrofs.modulus with Int.modulus.
      repeat rewrite <- Int.unsigned_repr_eq.
      set (Int_unsigned_ge_zero (pc_loc st)) as Heq.
      rewrite Int.repr_unsigned.
      rewrite Z2Nat.id; try lia.
      rewrite Int.unsigned_repr.
      - f_equal.
      - change Int.max_unsigned with Ptrofs.max_unsigned.
          change  Ptrofs.max_unsigned with 4294967295%Z in *.
          unfold upd_mem, upd_regs, HAVMState.upd_pc in *; simpl in Hkv_max, Hkv_len.
          rewrite Hkv_len in *.
          split; lia.
    }
    rewrite Heq in Hkv2; clear Heq.




      eapply Smallstep.star_step with (t1 := Events.E0) (t2 := Events.E0); eauto.
      { repeat (econstructor; eauto; try deref_loc_tactic).
        - unfold set_opttemp.
          rewrite Maps.PTree.gso; [| intro HF; inversion HF].
          eapply p0.
        - unfold set_opttemp.
          rewrite Maps.PTree.gso; [| intro HF; inversion HF].
          eapply p0.
        - rewrite Ptrofs.add_zero_l.
          unfold Coqlib.align; simpl.
          change (Ptrofs.unsigned (Ptrofs.repr (352 / 8))) with
            (Ptrofs.unsigned (Ptrofs.repr 44)).
          eapply mpc.
        - unfold set_opttemp.
          rewrite Maps.PTree.gso; [| intro HF; inversion HF].
          eapply p0.
        - rewrite Ptrofs.add_zero_l.
          unfold Coqlib.align; simpl.
          change (Ptrofs.unsigned (Ptrofs.repr (544 / 8))) with
            (Ptrofs.unsigned (Ptrofs.repr 68)).
          eapply Hload_kv.
        - unfold set_opttemp.
          rewrite Maps.PTree.gso; [| intro HF; inversion HF].
          eapply p0.
        - rewrite Ptrofs.add_zero_l.
          unfold Coqlib.align; simpl.
          change (Ptrofs.unsigned (Ptrofs.repr (352 / 8))) with
            (Ptrofs.unsigned (Ptrofs.repr 44)).
          eapply mpc.
        - unfold Cop.sem_binary_operation, Cop.sem_add; simpl.
          fold Ptrofs.zero.
          rewrite Ptrofs.add_zero_l.
          unfold Coqlib.align; simpl.
          reflexivity.
        - unfold Coqlib.align; simpl.
          change (32 / 8)%Z with 4%Z.
          rewrite Hkv2.
          eapply nth_error_nth with (d := empty_kv) in Hnth.
          rewrite Hnth.
          reflexivity.

        - unfold Cop.sem_binary_operation, Cop.sem_add, Cop.sem_binarith; simpl.
          reflexivity.

        - constructor.
        - rewrite Ptrofs.add_zero_l.
          unfold Coqlib.align; simpl.
          change (Ptrofs.unsigned (Ptrofs.repr (352 / 8))) with
            (Ptrofs.unsigned (Ptrofs.repr 44)).
          rewrite Hstore_m.
          reflexivity.
      }

      eapply Smallstep.star_step with (t1 := Events.E0) (t2 := Events.E0); eauto.
      { eapply step_skip_seq. }

      eapply Smallstep.star_step with (t1 := Events.E0) (t2 := Events.E0); eauto.
      { eapply step_return_0; try reflexivity. }
      eapply Smallstep.star_refl; eauto.
    }

    split_and.
    - unfold eval_inv, match_res; simpl.
      reflexivity.
    - constructor.
    - unfold upd_regs, upd_mem, HAVMState.upd_pc; simpl.
      inversion MS.
      split; simpl.
      + eapply rBPFMemType.store_unchanged_on_3; eauto.
        intros ofs HF.
        destruct HF as (HF & _).
        apply HF; reflexivity.
      + clear - Hcopy_from Hstore_m mregs0.
        unfold match_registers in *.
        intros r.
        specialize (mregs0 r).
        destruct mregs0 as (vr & Hload_r & Heval_r).
        
    - simpl; auto.
Qed.

End Upd_reg.

Existing Instance correct_function_upd_reg.
