From compcert.lib Require Import Integers Coqlib Maps.
From compcert.common Require Import AST Values Memory.
From compcert.arm Require Import AsmSyntax ABinSem BinDecode BinSyntax.

From bpf.comm Require Import JITCall.
From bpf.rbpf32 Require Import TSSyntax JITConfig.
From bpf.jit Require Import Arm32Reg ThumbInsOp ThumbJIT WholeCompiler.
From bpf.jit Require Import ThumbJITLtac ABMemory TSSemanticsB ThumbJITProofLemma0 TSSemanticsBproofdef.
From bpf.jit Require Import ThumbDecodeEncodeALU ThumbDecodeEncodeMEM.
From Coq Require Import ZArith Lia List ListSet.

Open Scope nat_scope.
Open Scope asm.
Import ListNotations.

Lemma exec_alu32_mov_r1:
  forall l2 dst ld_set st_set ld_set2 st_set2 (rs0 rs1: regset) i jit_blk st_blk m1 ars0 astk0 astkb am
    (Hsave : jit_call_save_reg dst dst ld_set st_set = (l2, ld_set2, st_set2))
    (HALU : rs0 dst = Vint i)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1)
            (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 =
           BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
             (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l2 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1)
          (AState ars1 astk1 astkb am).
Proof.
  intros.
  unfold jit_call_save_reg, jit_call_save_add in Hsave.
  rewrite set_add_same in Hsave.
  destruct set_mem eqn: Hdst_in.
  {
    rewrite app_nil_l in Hsave.
    apply set_mem_correct1 in Hdst_in.
    assert (Heq: set_mem breg_eq dst (set_add breg_eq dst ld_set) = true). {
      apply set_mem_correct2.
      apply set_add_intro2; reflexivity.
    }
    rewrite Heq in Hsave; clear Heq.
    injection Hsave as Hl2_eq Hld_eq Hst_eq.
    subst.
    simpl.
    exists ars0, astk0.
    split; [destruct is_final_state; reflexivity | ].

    inversion HST; subst.
    unfold match_regs in REG.
    specialize (REG dst) as REG_DST.
    destruct REG_DST as (REG_DST & _).

    assert (Hdst_in_union: In dst (set_union breg_eq ld_set st_set)). {
      apply set_union_intro1.
      unfold set_In; auto.
    }

    specialize (REG_DST Hdst_in_union).
    destruct REG_DST as (v_dst & Hdst_1 & Hdst_2).


    constructor; auto.
    - destruct HNoDup as (HNoDup1 & HNoDup2);
      split; apply set_add_nodup; auto.
    - intros r Hin.
      apply set_add_elim in Hin.
      destruct Hin as [Hin | Hin].
      + apply set_add_intro2; assumption.
      + apply set_add_intro1; apply HSUB; assumption.
    - unfold match_regs in *.
      intros r; specialize (REG r).
      destruct REG as (REG1 & REG2 & REG3).
      destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
      { (**r r = dst *)
        subst r.
        specialize (REG1 Hdst_in_union).
        destruct REG1 as (vr & Hvr1 & Hvr2).
        rewrite Hvr1 in Hdst_1.
        injection Hdst_1 as Heq; subst vr.
        split.
        - intro Hin.
          exists i.
          split; repeat abreg_solver.
          rewrite <- HALU; rewrite Hvr1; assumption.
        - split.
          + intro Hnot_in.
            exfalso.
            apply Hnot_in.
            apply set_union_intro2.
            apply set_add_intro2.
            auto.
          + intros Hnot_in.
            exfalso.
            apply Hnot_in.
            apply set_add_intro2.
            auto.
      }
      { (**r r <> dst *)
        split.
        - intros.
          assert (Heq: In r (set_union breg_eq ld_set st_set)). {
            apply set_union_elim in H.
            destruct H as [H | H].
            - apply set_add_elim in H.
              destruct H as [H | H]; [exfalso; apply Hr_neq; auto |].
              apply set_union_intro1; auto.
            - apply set_add_elim in H.
              destruct H as [H | H]; [exfalso; apply Hr_neq; auto |].
              apply set_union_intro2; auto.
          }
          specialize (REG1 Heq); clear Heq.
          destruct REG1 as (vr & Hvr1 & Hvr2).
          exists vr.
          split; repeat abreg_solver.
        - split.
          + intro HN.
            destruct HN as (HN1 & HN2).
            assert (Heq: ~ In r (set_union breg_eq ld_set st_set) 
              /\ In r rbpf_arm_callee_save). {
              split; auto.
              intro HF. apply HN1.
              apply set_union_elim in HF.
              destruct HF as [HF | HF].
              - apply set_union_intro1.
                apply set_add_intro1; auto.
              - apply set_union_intro2.
                apply set_add_intro1; auto.
            }
            specialize (REG2 Heq); clear Heq.
            repeat abreg_solver.
          + intro HN.
            assert (Heq: ~ In r st_set). {
              intro HF. apply HN.
              apply set_add_intro1; auto.
            }
            specialize (REG3 Heq); clear Heq.
            destruct REG3 as (vr & Hvr1 & Hvr2).
            exists vr.
            split; repeat abreg_solver.
      }
    - unfold match_stack in *.
      destruct STK as (INIT_STK & STK).
      split; [auto | ].
      intros r Hin.
      specialize (STK r Hin).
      destruct STK as (STK1 & STK2).
      split; intros Hin1.
      {
        apply STK1.
        apply set_union_elim in Hin1.
        destruct Hin1 as [Hin1 | Hin1].
        - apply set_add_elim in Hin1.
          destruct Hin1 as [Hin1 | Hin1].
          + subst r.
            apply set_union_intro1; auto.
          + apply set_union_intro1; auto.
        - apply set_add_elim in Hin1.
          destruct Hin1 as [Hin1 | Hin1].
          + subst r.
            apply set_union_intro1; auto.
          + apply set_union_intro2; auto.
      }
      {
        destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
        - (**r r = dst *)
          subst r.
          exfalso.
          apply Hin1.
          clear.
          apply set_union_intro2.
          apply set_add_intro2; auto.
        - (**r r <> dst *)
          repeat abreg_solver.
          apply STK2.
          split; auto.
          intro HF.
          apply Hin1.
          apply set_union_elim in HF.
          destruct HF as [HF | HF].
          + apply set_union_intro1.
            apply set_add_intro1; auto.
          + apply set_union_intro2.
            apply set_add_intro1; auto.
      }
  }

  apply set_mem_complete1 in Hdst_in.
  assert (Heq: set_mem breg_eq dst (set_add breg_eq dst ld_set) = true). {
    apply set_mem_correct2.
    apply set_add_intro2; auto.
  }
  rewrite Heq in Hsave; clear Heq.
  rewrite app_nil_r in Hsave.
  unfold jit_alu32_thumb_mem_template_jit in Hsave.

  inversion HST; subst.
  unfold match_regs in REG.
  specialize (REG dst) as HREG_DST.
  destruct HREG_DST as (REG1 & REG2 & REG3).
  assert (Heq: ~ In dst st_set). {
    intro HF; apply Hdst_in.
    apply HSUB; auto.
  }
  specialize (REG3 Heq); clear Heq.
  destruct REG3 as (v_dst & Hdst1 & Hdst2).

  unfold match_stack in STK.
  destruct STK as ((INIT_STK & INIT_STK1) & STK).
  destruct set_mem eqn: Hdst_callee in Hsave.
  {
    assert (Heq: ~ In dst (set_union breg_eq ld_set st_set) /\
      In dst rbpf_arm_callee_save). {
      split.
      - intro HF; apply Hdst_in.
        apply set_union_elim in HF.
        destruct HF as [HF | HF].
        + assumption.
        + apply HSUB.
          assumption.
      - apply set_mem_correct1 in Hdst_callee. auto.
    }
    specialize (REG2 Heq); clear Heq.

    injection Hsave as Hl2_eq Hld2_eq Hst2_eq; subst.
    simpl.

    assert (Heq: is_final_state ars0 = false). {
      unfold is_final_state.
      assert (Heq: aval_eq (ars0 IR13) (Aval (Rval (Sreg IR13))) = false).
      - rewrite HIR13.
        simpl.
        auto.
      - rewrite Heq.
        rewrite andb_false_r.
        rewrite andb_false_l.
        auto.
    }
    rewrite Heq; clear Heq.

    rewrite decode_str_i_13.
    simpl.

    rewrite HIR13. simpl. rewrite Ptrofs.add_zero_l.

    apply set_mem_correct1 in Hdst_callee.
    erewrite aexec_store_ir13; eauto.

    assert (Heq: is_final_state (anextinstr true ars0) = false). {
      unfold is_final_state.
      assert (Heq: aval_eq (anextinstr true ars0 IR13)
        (Aval (Rval (Sreg IR13))) = false).
      - unfold anextinstr.
        repeat abreg_solver_error_prone.
        rewrite HIR13.
        simpl.
        auto.
      - rewrite Heq.
        rewrite andb_false_r.
        rewrite andb_false_l.
        auto.
    }
    rewrite Heq; clear Heq.

    rewrite decode_ldr_i_12.
    remember (setN (encode_sval_fragments Cany32 (Rval (Sreg (ireg_of_breg dst))))
     (z_of_breg dst * 4) astk0) as astk1 eqn: Hastk1_eq.
    simpl.
    unfold anextinstr at 1. abreg_solver_error_prone.
    rewrite HIR12.
    simpl. rewrite Ptrofs.add_zero_l.

    rewrite ptr_int_mul_4.

    rewrite Hdst2.
    eexists. exists astk1.
    split; [destruct is_final_state; f_equal |].
    constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; simpl; repeat abreg_solver.
    + intros.
      specialize (Hfloat _ H).
      repeat float_preg_of_solver.
      repeat (destruct H as [H | H];
          [subst x; auto|]); inversion H.

    + destruct HNoDup as (HNoDup1 & HNoDup2);
      split; apply set_add_nodup; auto.
    + repeat abreg_solver_error_prone.
       destruct (ireg_eq IR0 (ireg_of_breg dst)) as [Hr_eq | Hr_neq].
        { (**r r = dst *)
          rewrite <- Hr_eq.
          repeat abreg_solver_error_prone.
          simpl.
          reflexivity.
        }
        { (**r r <> dst *)
          rewrite Pregmap.gso.
          2:{ intro HF. apply Hr_neq. injection HF as Heq. assumption. }
          repeat abreg_solver.
        }
    + clear - HAR11 Hastk1_eq.
      unfold astack_load in *.
      destruct Mem.valid_access_dec; [| inversion HAR11].
      subst astk1.
      rewrite ab_getN_setN_outside; [auto | ].
      right. simpl.
      destruct dst; simpl; lia.

    + destruct HIRPC as (va_pc & HIRPC).
      unfold aoffset_ptr.
      repeat abreg_solver_error_prone.
      rewrite Pregmap.gso. 2:{ unfold ireg_of_breg; intro HF; inversion HF. }
      rewrite Pregmap.gss.
      rewrite HIRPC.
      simpl.
      eexists; f_equal.

    + intros r Hin.
      apply set_add_elim in Hin.
      destruct Hin as [Hin | Hin].
      * subst r.
        apply set_add_intro2; reflexivity.
      * apply set_add_intro1.
        apply HSUB; auto.

    + unfold match_regs.
      intro r.
      clear REG1 REG2.
      specialize (REG r).
      destruct REG as (REG1 & REG2 & REG3).
      split.
      * intro Hin.
        destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
        { (**r r = dst *)
          subst r.
          exists i.
          split.
          - repeat abreg_solver.
          - repeat abreg_solver.
            rewrite <- HALU. rewrite Hdst1. simpl; auto.
        }
        { (**r r <> dst *)
          assert (Heq: In r (set_union breg_eq ld_set st_set)). {
            apply set_union_elim in Hin.
            destruct Hin as [Hin | Hin].
            - apply set_add_elim in Hin.
              destruct Hin as [Hin | Hin].
              + exfalso; apply Hr_neq; auto.
              + apply set_union_intro1; auto.
            - apply set_add_elim in Hin.
              destruct Hin as [Hin | Hin].
              + exfalso; apply Hr_neq; auto.
              + apply set_union_intro2; auto.
          }
          specialize (REG1 Heq); clear Heq.
          destruct REG1 as (vr_r & Hvr_r1 & Hvr_r2).
          exists vr_r.
          split; repeat abreg_solver.
        }
      * split; intro HF. destruct HF as (HF & HF1).
        { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
          { (**r r = dst *)
            subst r.
            exfalso; apply HF; clear.
            apply set_union_intro2.
            apply set_add_intro2; auto.
          }
          { (**r r <> dst *)
            assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
                In r rbpf_arm_callee_save). {
              split; auto.
              intro Hin; apply HF.
              apply set_union_elim in Hin.
              destruct Hin as [Hin | Hin].
              - apply set_union_intro1.
                apply set_add_intro1; auto.
              - apply set_union_intro2; apply set_add_intro1; auto.
            }
            specialize (REG2 Heq); clear Heq.

            rename HF into Hno_in.
            repeat abreg_solver.
          }
        }
        { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
          { (**r r = dst *)
            subst r.
            exfalso; apply HF; clear.
            apply set_add_intro2; auto.
          }
          { (**r r <> dst *)
            assert (Heq: ~ In r st_set). {
              intro Hin; apply HF.
              apply set_add_intro1; auto.
            }
            specialize (REG3 Heq); clear Heq.
            destruct REG3 as (vr3 & Hvr3 & Hvr4).
            exists vr3.
            rename HF into Hno_in.
            split; repeat abreg_solver.
          }
        }

    + split; [init_arm_stack_update1 | ].
      { intros r Hcallee.
        specialize (STK r Hcallee).
        destruct STK as (STK1 & STK2).
        split; intro Hin.
        - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
          { (**r r = dst *)
            subst r.

            subst astk1.
            unfold astack_load.

            destruct Mem.valid_access_dec as [HT | HF].
            - assert (Heq: List.length (encode_sval_fragments Cany32
                (Rval (Sreg (ireg_of_breg dst)))) = size_chunk_nat Many32). {
                unfold size_chunk_nat; simpl. auto.
              }
              rewrite <- Heq; clear Heq.
              rewrite ab_getN_setN_same. decode_val_same_breg_solver.
            - valid_access_fail_solver.
          }
          { (**r r <> dst *)
            assert (Heq: In r (set_union breg_eq ld_set st_set)). {
              apply set_union_elim in Hin.
              destruct Hin as [Hin | Hin].
              - apply set_add_elim in Hin.
                destruct Hin as [Hin | Hin].
                + exfalso; apply Hr_neq; inversion Hin; reflexivity.
                + apply set_union_intro1; auto.
              - apply set_add_elim in Hin.
                destruct Hin as [Hin | Hin].
                + exfalso; apply Hr_neq; inversion Hin; reflexivity.
                + apply set_union_intro2; auto.
            }
            specialize (STK1 Heq); clear Heq.
            subst astk1.
            rewrite <- STK1.
            unfold astack_load.
            destruct Mem.valid_access_dec; [| auto].
            rewrite ab_getN_setN_outside. f_equal.
            simpl.
            clear - Hr_neq.
            destruct r; destruct dst; simpl; try lia; exfalso; apply Hr_neq; reflexivity.
          }
        - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
          { (**r r = dst *)
            subst r.
            exfalso. clear - Hin.
            apply Hin.
            apply set_union_intro2. apply set_add_intro2; auto.
          }
          { (**r r <> dst *) destruct Hin as (Hin & Hin1).
            assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
              In r rbpf_arm_callee_save). {
              split; auto.
              rename Hin into HF.
              intro Hin; apply HF.
              apply set_union_elim in Hin.
              destruct Hin as [Hin | Hin].
              - apply set_union_intro1; apply set_add_intro1; auto.
              - apply set_union_intro2; apply set_add_intro1; auto.
            }
            specialize (STK2 Heq); clear Heq.
            repeat abreg_solver.
          }
      }
  }

  injection Hsave as Hl2_eq Hld2_eq Hst2_eq; subst.
  simpl.

  assert (Heq: is_final_state ars0 = false). {
    unfold is_final_state.
    assert (Heq: aval_eq (ars0 IR13) (Aval (Rval (Sreg IR13))) = false).
    - rewrite HIR13.
      simpl.
      auto.
    - rewrite Heq.
      rewrite andb_false_r.
      rewrite andb_false_l.
      auto.
  }
  rewrite Heq; clear Heq.

  rewrite decode_ldr_i_12.
  simpl.

  rewrite HIR12. simpl. rewrite Ptrofs.add_zero_l. rewrite ptr_int_mul_4.
  rewrite Hdst2.

  assert (Heq: is_final_state
    (anextinstr true ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) = false). {
    unfold is_final_state.
    assert (Heq: aval_eq (anextinstr true ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst)) IR13)
      (Aval (Rval (Sreg IR13))) = false).
    - unfold anextinstr.
      repeat abreg_solver_error_prone.
      rewrite HIR13.
      simpl.
      auto.
    - rewrite Heq.
      rewrite andb_false_r.
      rewrite andb_false_l.
      auto.
  }
  rewrite Heq; clear Heq.

  unfold anextinstr; simpl. repeat abreg_solver_error_prone.
  simpl.
  eexists. exists astk0.
  split; [f_equal |].

  constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; simpl; repeat abreg_solver.
  + intros.
    specialize (Hfloat _ H).
    repeat float_preg_of_solver.
    repeat (destruct H as [H | H];
        [subst x; auto|]); inversion H.
  + destruct HNoDup as (HNoDup1 & HNoDup2);
      split; apply set_add_nodup; auto.
  + repeat abreg_solver_error_prone.
     destruct (ireg_eq IR0 (ireg_of_breg dst)) as [Hr_eq | Hr_neq].
      { (**r r = dst *)
        rewrite <- Hr_eq.
        repeat abreg_solver_error_prone.
        simpl.
        reflexivity.
      }
      { (**r r <> dst *)
        rewrite Pregmap.gso.
        2:{ intro HF. apply Hr_neq. injection HF as Heq. assumption. }
        repeat abreg_solver.
      }

  + destruct HIRPC as (va_pc & HIRPC).
    unfold aoffset_ptr.
    repeat abreg_solver_error_prone.
    rewrite Pregmap.gso. 2:{ unfold ireg_of_breg; intro HF; inversion HF. }
    rewrite HIRPC.
    simpl.
    eexists; f_equal.

  + intros r Hin.
    apply set_add_elim in Hin.
    destruct Hin as [Hin | Hin].
    * subst r.
      apply set_add_intro2; reflexivity.
    * apply set_add_intro1.
      apply HSUB; auto.

  + unfold match_regs.
    intro r.
    clear REG1 REG2.
    specialize (REG r).
    destruct REG as (REG1 & REG2 & REG3).
    split.
    * intro Hin.
      destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
      { (**r r = dst *)
        subst r.
        exists i.
        split; repeat abreg_solver.
        rewrite <- HALU. rewrite Hdst1. simpl; auto.
      }
      { (**r r <> dst *)
        assert (Heq: In r (set_union breg_eq ld_set st_set)). {
          apply set_union_elim in Hin.
          destruct Hin as [Hin | Hin].
          - apply set_add_elim in Hin.
            destruct Hin as [Hin | Hin].
            + exfalso; apply Hr_neq; auto.
            + apply set_union_intro1; auto.
          - apply set_add_elim in Hin.
            destruct Hin as [Hin | Hin].
            + exfalso; apply Hr_neq; auto.
            + apply set_union_intro2; auto.
        }
        specialize (REG1 Heq); clear Heq.
        destruct REG1 as (vr_r & Hvr_r1 & Hvr_r2).
        exists vr_r.
        split; repeat abreg_solver.
      }
    * split; intro HF. destruct HF as (HF & HF1).
      { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
        { (**r r = dst *)
          subst r.
          exfalso; apply HF; clear.
          apply set_union_intro2.
          apply set_add_intro2; auto.
        }
        { (**r r <> dst *)
          assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
              In r rbpf_arm_callee_save). {
            split; auto.
            intro Hin; apply HF.
            apply set_union_elim in Hin.
            destruct Hin as [Hin | Hin].
            - apply set_union_intro1.
              apply set_add_intro1; auto.
            - apply set_union_intro2; apply set_add_intro1; auto.
          }
          specialize (REG2 Heq); clear Heq.

          rename HF into Hno_in.
          repeat abreg_solver.
        }
      }
      { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
        { (**r r = dst *)
          subst r.
          exfalso; apply HF; clear.
          apply set_add_intro2; auto.
        }
        { (**r r <> dst *)
          assert (Heq: ~ In r st_set). {
            intro Hin; apply HF.
            apply set_add_intro1; auto.
          }
          specialize (REG3 Heq); clear Heq.
          destruct REG3 as (vr3 & Hvr3 & Hvr4).
          exists vr3.
          rename HF into Hno_in.
          split; repeat abreg_solver.
        }
      }

  + split; [split; assumption | ].
    { intros r Hcallee.
      specialize (STK r Hcallee).
      destruct STK as (STK1 & STK2).
      split; intro Hin.
      - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
        { (**r r = dst *)
          subst r.
          exfalso.
          clear - Hdst_callee Hcallee.
          apply set_mem_arm_callee_save_false in Hdst_callee.
          apply Hdst_callee. auto.
        }
        { (**r r <> dst *)
          apply STK1.
          apply set_union_elim in Hin.
          destruct Hin as [Hin | Hin].
          - apply set_add_elim in Hin.
            destruct Hin as [Hin | Hin].
            + exfalso; apply Hr_neq; inversion Hin; reflexivity.
            + apply set_union_intro1; auto.
          - apply set_add_elim in Hin.
            destruct Hin as [Hin | Hin].
            + exfalso; apply Hr_neq; inversion Hin; reflexivity.
            + apply set_union_intro2; auto.
        }
      - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
        { (**r r = dst *)
          subst r.
          exfalso. clear - Hin.
          apply Hin.
          apply set_union_intro2. apply set_add_intro2; auto.
        }
        { (**r r <> dst *) destruct Hin as (Hin & Hin1).
          assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
              In r rbpf_arm_callee_save). {
            split; auto.
            rename Hin into HF.
            intro Hin; apply HF.
            apply set_union_elim in Hin.
            destruct Hin as [Hin | Hin].
            - apply set_union_intro1; apply set_add_intro1; auto.
            - apply set_union_intro2; apply set_add_intro1; auto.
          }
          specialize (STK2 Heq); clear Heq.
          repeat abreg_solver.
        }
    }
Qed.