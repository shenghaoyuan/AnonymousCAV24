From compcert Require Import Memory Memtype Integers Values Ctypes AST.
From Coq Require Import ZArith Lia List Logic.FunctionalExtensionality.

From bpf.comm Require Import Flag rBPFValues Regs BinrBPF MemRegion rBPFAST rBPFMemType ListAsArray Monad.

From bpf.rbpf32 Require Import BState BSemanticsMonadic BSemanticsSimpl BStateMonadOp.
Import ListNotations.

Lemma check_mem_aux2_eq:
  forall p addr chunk m st1,
    BSemanticsMonadic.check_mem_aux2 m p addr chunk st1 =
      Some (check_mem_aux2 m p addr chunk, st1).
Proof.
  unfold BSemanticsMonadic.check_mem_aux2, check_mem_aux2, bindM, returnM, Monad.bindM, Monad.returnM; intros.
  unfold get_start_addr, get_block_size, get_block_perm, get_sub, get_add, returnM, Monad.returnM.
  match goal with
  | |- (if ?X then _ else _) _ = _ =>
    destruct X; f_equal
  end.
Qed.

Lemma check_mem_aux_simpl_equiv:
  forall n p addr chunk st1 st2 ptr mrs
  (Hcheck: BSemanticsMonadic.check_mem_aux n p chunk addr mrs st1 =
         Some (ptr, st2)),
    check_mem_aux n (mrs_num st1) p chunk addr mrs (bpf_m st1) = Some ptr /\
    st1 = st2.
Proof.
  induction n; simpl; unfold bindM, returnM, Monad.bindM, Monad.returnM; intros.
  { inversion Hcheck; subst; auto. }

  unfold get_mem_region in Hcheck.
  unfold BState.get_mem_region in *.
  destruct ((_ <? _)%nat); [| inversion Hcheck].
  destruct nth_error; [| inversion Hcheck].

  rewrite check_mem_aux2_eq in Hcheck.
  unfold cmp_ptr32_nullM in Hcheck.
  destruct cmp_ptr32_null as [check_ptr| ]; [| inversion Hcheck].
  destruct check_ptr.
  + eapply IHn; eauto.
  + inversion Hcheck; subst; simpl; auto.
Qed.

Lemma check_mem_simpl_equiv:
  forall p addr chunk st1 st2 ptr
  (Hcheck: BSemanticsMonadic.check_mem p chunk addr st1 = Some (ptr, st2)),
    check_mem p chunk addr
      (mrs_num st1) (bpf_mrs st1) (bpf_m st1) = Some ptr /\
    st1 = st2.
Proof.
  unfold BSemanticsMonadic.check_mem, check_mem, bindM, returnM, Monad.bindM, Monad.returnM; intros.

  unfold eval_mem_num, eval_mem_regions in Hcheck.
  destruct BSemanticsMonadic.check_mem_aux as [(ptr', st')|] eqn: Heq;
    [| inversion Hcheck].
  eapply check_mem_aux_simpl_equiv in Heq; eauto.
  destruct Heq as (Heq & Heq1); subst st'.
  rewrite Heq.
  unfold cmp_ptr32_nullM in Hcheck.
  destruct cmp_ptr32_null; [| inversion Hcheck].
  destruct b; inversion Hcheck; auto.
Qed.

(*
Axiom lemma_bpf_get_call_simpl :
  forall i st1,
    rBPFMonadOp._bpf_get_call (Vint i) st1 = Some (_bpf_get_call (Vint i), st1).

Axiom lemma_exec_function_simpl :
  forall b ofs st1,
    exists st2, rBPFMonadOp.exec_function (Vptr b ofs) st1 = Some (exec_function (Vptr b ofs), st2) /\
      pc_loc st1 = pc_loc st2 /\ regs_st st1 = regs_st st2 /\
      bpf_m st1 = bpf_m st2 /\ flag st1 = flag st2 /\
      ins st1 = ins st2 /\ ins_len st1 = ins_len st2 /\
      mrs_num st1 = mrs_num st2 /\ bpf_mrs st1 = bpf_mrs st2. *)

Lemma step_simpl_unchanged:
  forall st1 st2 vt
  (Haux: BSemanticsMonadic.step st1 = Some (vt, st2)),
    ins st1 = ins st2 /\ ins_len st1 = ins_len st2 /\
      mrs_num st1 = mrs_num st2 /\ bpf_mrs st1 = bpf_mrs st2 /\
      tp_kv st1 = tp_kv st2 /\ tp_bin st1 = tp_bin st2.
Proof.
  unfold BSemanticsMonadic.step, step, bindM, returnM, Monad.bindM, Monad.returnM; intros.
  unfold eval_ins, BState.eval_ins, List64AsArray.index in Haux.
  destruct (regs_st st1 TSSyntax.BPC); inversion Haux.
  clear H0.
  destruct Int.cmpu; [| inversion Haux].
  destruct nth_error; [| inversion Haux].
  unfold decodeM in Haux.
  destruct TSDecode.decode_ind as [ins | ]; [| inversion Haux].
  destruct ins.
  - unfold BSemanticsMonadic.step_load_x_operation, eval_mem, eval_reg, upd_flag, eval_mem_regions,
      get_addr_ofs, cmp_ptr32_nullM, bindM, returnM, Monad.bindM, Monad.returnM in Haux.
    destruct BSemanticsMonadic.check_mem as [ (check_ptr & stk) |] eqn: Hcheck; [| inversion Haux].
    eapply check_mem_simpl_equiv in Hcheck as Hcheck_simpl; eauto.
    destruct Hcheck_simpl as (Heq_mem & Heq_st).
    subst stk.
    destruct cmp_ptr32_null as [ cond |]; [ destruct cond | inversion Haux].
    + inversion Haux; subst; simpl.
      intuition.
    + unfold upd_reg, load_mem, BState.load_mem in Haux.
      destruct s; simpl in Haux; inversion Haux; clear H0.
      {
        destruct Mem.loadv as [lv| ]; [| inversion Haux].
        destruct lv as [| vi | vl | vf | vs | vp]; inversion Haux; simpl;
          intuition.
      }
      {
        destruct Mem.loadv as [lv| ]; [| inversion Haux].
        destruct lv as [| vi | vl | vf | vs | vp]; inversion Haux; simpl;
          intuition.
      }
      {
        destruct Mem.loadv as [lv| ]; [| inversion Haux].
        destruct lv as [| vi | vl | vf | vs | vp]; inversion Haux; simpl;
          intuition.
      }

  - unfold BSemanticsMonadic.step_store_operation, eval_mem, eval_reg, upd_flag,
    eval_mem_regions, BState.eval_reg, get_addr_ofs, BState.upd_flag, cmp_ptr32_nullM,
    store_mem, BState.store_mem, bindM, returnM, Monad.bindM, Monad.returnM in Haux.
    destruct s0.
    {
      destruct BSemanticsMonadic.check_mem as [ (check_ptr & stk) |] eqn: Hcheck; [| inversion Haux].
      eapply check_mem_simpl_equiv in Hcheck as Hcheck_simpl; eauto.
      destruct Hcheck_simpl as (Heq_mem & Heq_st).
      subst stk.
      destruct cmp_ptr32_null as [ cond |]; [ destruct cond | inversion Haux].
      + inversion Haux; subst; simpl.
        intuition.
      + unfold upd_reg in Haux.
        destruct s; simpl in Haux; inversion Haux; clear H0.
        {
          destruct Mem.storev as [lv| ]; [| inversion Haux].
          inversion Haux; simpl;
          intuition.
        }
        {
          destruct Mem.storev as [lv| ]; [| inversion Haux].
          inversion Haux; simpl;
          intuition.
        }
        {
          destruct Mem.storev as [lv| ]; [| inversion Haux].
          inversion Haux; simpl;
          intuition.
        }
    }

    destruct BSemanticsMonadic.check_mem as [ (check_ptr & stk) |] eqn: Hcheck; [| inversion Haux].
    eapply check_mem_simpl_equiv in Hcheck as Hcheck_simpl; eauto.
    destruct Hcheck_simpl as (Heq_mem & Heq_st).
    subst stk.
    destruct cmp_ptr32_null as [ cond |]; [ destruct cond | inversion Haux].
    + inversion Haux; subst; simpl.
      intuition.
    + unfold upd_mem in Haux.
      destruct s; simpl in Haux; inversion Haux; clear H0.
      {
        destruct Mem.storev as [lv| ]; [| inversion Haux].
        inversion Haux; simpl;
        intuition.
      }
      {
        destruct Mem.storev as [lv| ]; [| inversion Haux].
        inversion Haux; simpl;
        intuition.
      }
      {
        destruct Mem.storev as [lv| ]; [| inversion Haux].
        inversion Haux; simpl;
        intuition.
      }

  - unfold jit_call_simplb, BState.jit_call_simplb in Haux.
    destruct regs_st; inversion Haux; clear H0.
    destruct ListNat.index; [| inversion Haux].
    destruct Mem.alloc.
    destruct JITConfig.copy_to; [| inversion Haux].
    destruct ABinSem.bin_exec as [(res & m3)|]; [| inversion Haux].
    destruct JITConfig.copy_from; [| inversion Haux].
    inversion Haux; subst.
    unfold upd_mem, BState.upd_regs; simpl; auto.
    intuition.

  - unfold upd_pc, upd_pc_incr in Haux.
    inversion Haux; subst; unfold BState.upd_regs, BState.upd_pc; simpl; auto.
    intuition.

  - unfold eval_cmp, upd_pc, upd_pc_incr in Haux.
    destruct BState.eval_cmp; [| inversion Haux].
    destruct b0;
    inversion Haux; subst; unfold BState.upd_regs, BState.upd_pc; simpl; auto;
    intuition.

  - unfold _bpf_get_call in Haux.
    destruct BState._bpf_get_call as [(v & m)|]; [| inversion Haux].
    unfold upd_reg, upd_mem, upd_pc_incr in Haux.
    destruct v; inversion Haux; subst; unfold BState.upd_regs, BState.upd_pc; simpl; auto;
    intuition.

  - unfold upd_flag in Haux.
    inversion Haux; unfold BState.upd_flag; subst; simpl; auto.
    intuition.
Qed.


Lemma step_simpl_equiv:
  forall st1 st2 vt
  (Hflag_eq: flag st1 = BPF_OK)
  (Haux: BSemanticsMonadic.step st1 = Some (vt, st2)),
    step (ins st1) (tp_kv st1) (ins_len st1) (regs_st st1) (mrs_num st1) (bpf_mrs st1) 
      (bpf_m st1) = Some ((regs_st st2), (bpf_m st2), (flag st2)).
Proof.
  unfold BSemanticsMonadic.step, step, bindM, returnM, Monad.bindM, Monad.returnM; intros.
  unfold eval_ins, BState.eval_ins, List64AsArray.index in Haux.
  unfold BSemanticsSimpl.eval_ins.
  destruct (regs_st st1 TSSyntax.BPC) eqn: Hpc_eq; inversion Haux; clear H0.
  destruct Int.cmpu; [| inversion Haux].
  destruct nth_error; [| inversion Haux].
  unfold decodeM in Haux.
  destruct TSDecode.decode_ind as [ins | ]; [| inversion Haux].
  destruct ins.
  - unfold BSemanticsMonadic.step_load_x_operation, eval_mem, eval_reg, upd_flag,
      get_addr_ofs, cmp_ptr32_nullM, eval_mem_regions, bindM, returnM in Haux.
    unfold Monad.bindM, BState.eval_reg, Monad.returnM, BState.upd_flag in Haux.
    unfold step_load_x_operation, load_mem.
    destruct BSemanticsMonadic.check_mem as [ (check_ptr & stk) |] eqn: Hcheck; [| inversion Haux].
    eapply check_mem_simpl_equiv in Hcheck as Hcheck_simpl; eauto.
    destruct Hcheck_simpl as (Heq_mem & Heq_st); subst stk.
    rewrite Heq_mem; clear Heq_mem.

    destruct cmp_ptr32_null as [ cond |]; [ destruct cond | inversion Haux].
    + inversion Haux; subst; simpl.
      f_equal.
    + unfold load_mem, BState.load_mem in Haux.
      unfold BSemanticsSimpl.load_mem.
      destruct s; simpl in *; inversion Haux; clear H0.
      {
        destruct Mem.loadv as [lv| ]; [| inversion Haux].
        destruct lv as [| vi | vl | vf | vs | vp]; inversion Haux; simpl.
        rewrite <- Hflag_eq.
        f_equal.
      }
      {
        destruct Mem.loadv as [lv| ]; [| inversion Haux].
        destruct lv as [| vi | vl | vf | vs | vp]; inversion Haux; simpl.
        rewrite <- Hflag_eq.
        f_equal.
      }
      {
        destruct Mem.loadv as [lv| ]; [| inversion Haux].
        destruct lv as [| vi | vl | vf | vs | vp]; inversion Haux; simpl.
        rewrite <- Hflag_eq.
        f_equal.
      }

  - unfold BSemanticsMonadic.step_store_operation, eval_mem, eval_reg, upd_flag,
      get_addr_ofs, cmp_ptr32_nullM, eval_mem_regions, bindM, returnM in Haux.
    unfold Monad.bindM, BState.eval_reg, Monad.returnM, BState.upd_flag in Haux.

    unfold step_store_operation, store_mem.

    destruct s0.
    {
      destruct BSemanticsMonadic.check_mem as [ (check_ptr & stk) |] eqn: Hcheck; [| inversion Haux].
      eapply check_mem_simpl_equiv in Hcheck as Hcheck_simpl; eauto.
      destruct Hcheck_simpl as (Hcheck_simpl & Heq_st); subst stk.
      rewrite Hcheck_simpl; clear Hcheck_simpl.

      destruct cmp_ptr32_null as [ cond |]; [ destruct cond | inversion Haux].
      + inversion Haux; subst; simpl.
        f_equal.
      + unfold store_mem, BState.store_mem in Haux.
        unfold BSemanticsSimpl.store_mem.
        unfold upd_pc_incr, upd_mem in Haux.
        destruct s; simpl in *; inversion Haux; clear H0.
        {
          destruct Mem.storev as [lv| ]; [| inversion Haux];
          unfold upd_mem in *;
          inversion Haux; subst; simpl;
          rewrite <- Hflag_eq;
          f_equal.
        }
        {
          destruct Mem.storev as [lv| ]; [| inversion Haux];
          unfold upd_mem in *;
          inversion Haux; subst; simpl;
          rewrite <- Hflag_eq;
          f_equal.
        }
        {
          destruct Mem.storev as [lv| ]; [| inversion Haux];
          unfold upd_mem in *;
          inversion Haux; subst; simpl;
          rewrite <- Hflag_eq;
          f_equal.
        }
    }

    destruct BSemanticsMonadic.check_mem as [ (check_ptr & stk) |] eqn: Hcheck; [| inversion Haux].
    eapply check_mem_simpl_equiv in Hcheck as Hcheck_simpl; eauto.
    destruct Hcheck_simpl as (Hcheck_simpl & Heq_st); subst stk.
    rewrite Hcheck_simpl; clear Hcheck_simpl.

    destruct cmp_ptr32_null as [ cond |]; [ destruct cond | inversion Haux].
    + inversion Haux; subst; simpl.
      f_equal.
    + unfold store_mem, upd_pc_incr, BState.store_mem in Haux.
      unfold BSemanticsSimpl.store_mem.
      destruct s; simpl in *; inversion Haux; clear H0.
      {
        destruct Mem.storev as [lv| ]; [| inversion Haux].
        inversion Haux; subst; simpl.
        rewrite <- Hflag_eq.
        f_equal.
      }
      {
        destruct Mem.storev as [lv| ]; [| inversion Haux].
        inversion Haux; subst; simpl.
        rewrite <- Hflag_eq.
        f_equal.
      }
      {
        destruct Mem.storev as [lv| ]; [| inversion Haux].
        inversion Haux; subst; simpl.
        rewrite <- Hflag_eq.
        f_equal.
      }

  - unfold jit_call_simplb in Haux.
    destruct BState.jit_call_simplb as [(rs & m)|]; [| inversion Haux].
    unfold BState.upd_regs in Haux; inversion Haux; subst; simpl.
    rewrite Hflag_eq.
    auto.

  - unfold upd_pc, upd_pc_incr, TSSyntax.nextinstr in Haux.
    inversion Haux; subst; simpl; auto.
    rewrite Hflag_eq.
    f_equal. f_equal. f_equal.
    rewrite TSSyntax.BPregmap.gss.
    extensionality r.
    destruct r eqn: Heq.
    + rewrite TSSyntax.BPregmap.gso; [| intro HF; inversion HF].
      subst r.
      rewrite TSSyntax.BPregmap.gso; [| intro HF; inversion HF].
      rewrite TSSyntax.BPregmap.gso; [| intro HF; inversion HF].
      auto.
    + rewrite TSSyntax.BPregmap.gss. rewrite TSSyntax.BPregmap.gss.
      unfold Vone. rewrite Hpc_eq. simpl. f_equal.

  - unfold eval_cmp, BState.eval_cmp in Haux.
    destruct TSSyntax.eval_cmp; [| inversion Haux].
    unfold upd_pc, upd_pc_incr, BState.upd_regs, BState.upd_pc in Haux.
    destruct b0; inversion Haux; subst; simpl in *.
    + unfold TSSyntax.nextinstr.
      rewrite TSSyntax.BPregmap.gss.
      f_equal.
      rewrite Hflag_eq; f_equal. f_equal.
      extensionality r.
      destruct r eqn: Heq.
      * rewrite TSSyntax.BPregmap.gso; [| intro HF; inversion HF].
        subst r.
        rewrite TSSyntax.BPregmap.gso; [| intro HF; inversion HF].
        rewrite TSSyntax.BPregmap.gso; [| intro HF; inversion HF].
        auto.
      * rewrite TSSyntax.BPregmap.gss. rewrite TSSyntax.BPregmap.gss.
        unfold Vone. rewrite Hpc_eq. simpl. f_equal.
    + rewrite Hflag_eq; repeat f_equal.

  - unfold _bpf_get_call, upd_reg in Haux.
    destruct BState._bpf_get_call as [(v & m)|]; [| inversion Haux].
    destruct v; inversion Haux; clear H0; simpl.
    rewrite Hflag_eq.
    f_equal.

  - unfold upd_flag in Haux.
    inversion Haux.
    f_equal.
Qed.

Lemma bpf_interpreter_aux_simpl_equiv:
  forall fuel st1 st2 vt
  (Hflag_eq: flag st1 = BPF_OK)
  (Haux: BSemanticsMonadic.bpf_interpreter_aux fuel st1 =
       Some (vt, st2)),
    bpf_interpreter_aux fuel (ins st1) (ins_len st1) (tp_kv st1) (tp_bin st1)
      (regs_st st1) (mrs_num st1) (bpf_mrs st1)
      (bpf_m st1) = Some ((regs_st st2), (bpf_m st2), (flag st2)).
Proof.
  induction fuel; simpl; unfold bindM, returnM, Monad.bindM, Monad.returnM; intros.
  {
    unfold upd_flag in Haux.
    unfold BState.upd_flag in Haux;
    inversion Haux; subst; f_equal.
  }

  destruct BSemanticsMonadic.step as [(rt & stk)|] eqn: Hstep; [| inversion Haux].
  eapply step_simpl_equiv in Hstep as Hstep_simpl; eauto; simpl in Hstep_simpl.
  rewrite Hstep_simpl; clear Hstep_simpl.

  unfold eval_flag in Haux.

  destruct flag_eq eqn: Hflag.
  - eapply step_simpl_unchanged in Hstep as Hstep_eq.
    destruct Hstep_eq as (Hins_eq & Hlen_eq & Hnum_eq & Hmrs_eq & Hkv_eq & Hbin_eq).
    rewrite Hins_eq, Hlen_eq, Hnum_eq, Hmrs_eq, Hkv_eq, Hbin_eq.
    eapply IHfuel; eauto.
    unfold flag_eq in Hflag.
    destruct (flag stk); inversion Hflag.
    reflexivity.
  - inversion Haux; subst; f_equal.
Qed.

Theorem bpf_interpreter_simpl_equiv:
  forall fuel ctx_ptr st1 res st2 v
  (Hflag_eq: flag st1 = BPF_OK)
  (Hctx: ctx_ptr = Vint v)
  (Hinterp: BSemanticsMonadic.bpf_interpreter fuel ctx_ptr st1 = Some (res, st2)),
    bpf_interpreter fuel ctx_ptr (ins st1) (ins_len st1) (tp_kv st1) (tp_bin st1)
      (regs_st st1) (mrs_num st1) (bpf_mrs st1) (bpf_m st1) =
    Some (res, (regs_st st2), (bpf_m st2), (flag st2)).
Proof.
  unfold BSemanticsMonadic.bpf_interpreter, bpf_interpreter, upd_reg, bindM, returnM, Monad.bindM, Monad.returnM.
  intros.
  subst ctx_ptr.
  simpl in *.
  destruct BSemanticsMonadic.bpf_interpreter_aux as [(vt & st')|] eqn: Haux; [| inversion Hinterp].
  eapply bpf_interpreter_aux_simpl_equiv in Haux; eauto.

  unfold BState.upd_reg in Haux; simpl in Haux.
  simpl.
  rewrite Haux.

  destruct flag_eq; inversion Hinterp; subst; f_equal.
Qed.