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

Lemma exec_alu32_mov_r_neq_dst_in_ld_set:
  forall l2 (dst src: breg) l1 ld_set st_set ld_set2 st_set2
    (rs0 rs1: regset) i jit_blk st_blk m1 ars0 astk0 astkb am
    (HALU : rs0 src = Vint i)
    (Hdst_in : set_mem breg_eq dst ld_set = true)
    (Hl2 :
      (if set_mem breg_eq src (set_add breg_eq dst ld_set)
       then []
       else
        if set_mem ireg_eq (ireg_of_breg src) arm_callee_save
        then
         [jit_alu32_thumb_mem_template_jit STR_I_OP (int_of_breg src) 
            (int_of_ireg IR13) (Int.mul (int_of_breg src) (Int.repr 4));
         jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg src) 
           (int_of_ireg IR12) (Int.mul (int_of_breg src) (Int.repr 4))]
        else
         [jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg src) 
            (int_of_ireg IR12) (Int.mul (int_of_breg src) (Int.repr 4))]) = l2)
    (Hld2 : set_add breg_eq src (set_add breg_eq dst ld_set) = ld_set2)
    (Hst2 : set_add breg_eq dst st_set = st_set2)
    (Hl1 : l2 ++
      [encode_arm32
         (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
            (encode_arm32 (int_of_ireg (ireg_of_breg src))
               (encode_arm32
                  (if Int.lt (int_of_breg dst) (Int.repr 8)
                   then int_of_breg dst
                   else Int.sub (int_of_breg dst) (Int.repr 8)) MOV_R_OP 0 3) 3 4) 7 1) NOP_OP 16
         16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 =
       BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
         (BPregmap.set dst (Vint i) rs0))
    (Hreg_neq : dst <> src),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  intros.

  inversion HST; subst.
  unfold match_regs in REG.
  specialize (REG dst) as REG_DST.
  specialize (REG src) as REG_SRC.
  apply set_mem_correct1 in Hdst_in.
  unfold set_In in Hdst_in.
  destruct REG_DST as (REG_DST1 & REG_DST2 & REG_DST3).
  destruct REG_SRC as (REG_SRC1 & REG_SRC2 & REG_SRC3).

  assert (Hdst_in_union: In dst (set_union breg_eq ld_set st_set)). {
    apply set_union_intro1.
    unfold set_In; auto.
  }
  specialize (REG_DST1 Hdst_in_union).
  destruct REG_DST1 as (v_dst & Hdst1 & Hdst2).

  unfold jit_alu32_thumb_mem_template_jit.

  unfold match_stack in *.
  destruct STK as ((INIT_STK1 & INIT_STK2) & STK).

  destruct set_mem eqn: Hsrc_in.
  - (**r src in ld_set *)
    rewrite app_nil_l.
    simpl.
    rewrite decode_mov_r.
    simpl.

    apply set_mem_correct1 in Hsrc_in.
    apply set_add_elim in Hsrc_in.
    destruct Hsrc_in as [Hsrc_in | Hsrc_in]; [exfalso; apply Hreg_neq; auto |].
    assert (Hsrc_in_union: In src (set_union breg_eq ld_set st_set)). {
      apply set_union_intro1.
      unfold set_In; auto.
    }

    specialize (REG_SRC1 Hsrc_in_union).
    destruct REG_SRC1 as (v_src & Hsrc1 & Hsrc2).
    rewrite Hdst2, Hsrc2 in *.
    simpl.
    eexists; eexists.
    split; [f_equal |].
    constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; repeat abreg_solver.
    + intros r Hin.
      apply set_add_elim in Hin.
      destruct Hin as [Hin | Hin].
      * subst r.
        apply set_add_intro1; apply set_add_intro2; auto.
      * specialize (HSUB _ Hin).
        apply set_add_intro1.
        apply set_add_intro1; auto.
    + unfold match_regs.
      intros.
      specialize (REG r).
      destruct REG as (REG1 & REG2 & REG3).
      destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
      { (**r r = dst *)
        subst r.
        specialize (REG1 Hdst_in_union).
        destruct REG1 as (vr & Hvr1 & Hvr2).
        rewrite Hvr1 in Hdst1.
        injection Hdst1 as Heq; subst vr.
        split.
        - intro Hin.
          exists i.
          split; repeat abreg_solver. rewrite <- HALU, Hsrc1. f_equal.
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
      destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
      { (**r r = src *)
        subst r.
        specialize (REG1 Hsrc_in_union).
        destruct REG1 as (vr & Hvr1 & Hvr2).
        rewrite Hvr1 in Hsrc1.
        injection Hsrc1 as Heq; subst vr.
        split.
        - intro Hin.
          exists v_src.
          split; repeat abreg_solver.
        - split.
          + intro Hnot_in.
            exfalso.
            apply Hnot_in.
            apply set_union_intro1.
            apply set_add_intro2.
            auto.
          + intros Hnot_in.
            assert (Heq: ~ In src st_set). {
              intro HF; apply Hnot_in. apply set_add_intro1; auto.
            }
            specialize (REG3 Heq); clear Heq.
            destruct REG3 as (vr & Hvr3 & Hvr4).
            exists vr.
            split; repeat abreg_solver.
      }
      { (**r r <> dst /\ r <> src *)
        split.
        - intros.
          assert (Heq: In r (set_union breg_eq ld_set st_set)). {
            apply set_union_elim in H.
            destruct H as [H | H].
            - apply set_add_elim in H.
              destruct H as [H | H]; [exfalso; apply Hr_neq_src; auto |].
              apply set_add_elim in H.
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
            assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
              intro HF. apply HN.
              apply set_union_elim in HF.
              destruct HF as [HF | HF].
              - apply set_union_intro1.
                apply set_add_intro1.
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

    + split; [split; auto | ].
      intros.
      specialize (STK r H).
      destruct STK as (STK1 & STK2).
      split; intros.
      {
        apply STK1.
        apply set_union_elim in H0.
        destruct H0 as [H0 | H0].
        - apply set_add_elim in H0.
          destruct H0 as [H0 | H0].
          + subst r.
            apply set_union_intro1; auto.
          + apply set_add_elim in H0.
            destruct H0 as [H0 | H0].
            * subst r.
              apply set_union_intro1; auto.
            * apply set_union_intro1; auto.
        - apply set_add_elim in H0.
          destruct H0 as [H0 | H0].
          + subst r.
            apply set_union_intro1; auto.
          + apply set_union_intro2; auto.
      }
      {
        destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
        - (**r r = dst *)
          subst r.
          exfalso.
          apply H0.
          clear.
          apply set_union_intro2.
          apply set_add_intro2; auto.
        - (**r r <> dst *)
          repeat abreg_solver.
          apply STK2.
          intro HF.
          apply H0.
          apply set_union_elim in HF.
          destruct HF as [HF | HF].
          + apply set_union_intro1.
            apply set_add_intro1.
            apply set_add_intro1; auto.
          + apply set_union_intro2.
            apply set_add_intro1; auto.
      }
  - (**r src not in ld_set *)
    apply set_mem_complete1 in Hsrc_in.

    assert (Heq: ~In src ld_set). {
      intro HF; apply Hsrc_in.
      apply set_add_intro1; auto.
    }
    clear Hsrc_in; rename Heq into Hsrc_in.


    assert (Heq: ~ In src st_set). {
      intro HF; apply Hsrc_in.
      apply HSUB.
      auto.
    }
    specialize (REG_SRC3 Heq); clear Heq.
    destruct REG_SRC3 as (v_src & Hsrc1 & Hsrc2).

    assert (Heq: ~ In src (set_union breg_eq ld_set st_set)). {
      intro HF; apply Hsrc_in.
      apply set_union_elim in HF.
      destruct HF as [HF | HF].
      - assumption.
      - apply HSUB.
        assumption.
    }
    specialize (REG_SRC2 Heq); clear Heq.

    destruct set_mem eqn: Hcallee.
    {
      apply set_mem_correct1 in Hcallee.
      simpl.
      rewrite decode_str_i_13.
      simpl.

      rewrite HIR13. simpl. rewrite Ptrofs.add_zero_l.
      erewrite aexec_store_ir13; eauto.

      rewrite decode_ldr_i_12.
      remember (setN (encode_sval_fragments Cany32 (Rval (Sreg (ireg_of_breg _))))
       _ astk0) as astk1 eqn: Hastk1_eq.
      simpl.
      unfold anextinstr at 1. repeat abreg_solver_error_prone.
      rewrite HIR12.
      simpl. rewrite Ptrofs.add_zero_l.

      rewrite ptr_int_mul_4.

      rewrite Hsrc2.
      rewrite decode_mov_r.
      unfold anextinstr; simpl. repeat abreg_solver_error_prone.

      simpl.
      eexists. exists astk1.
      split; [f_equal |].

      constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; simpl; repeat abreg_solver.
      + clear - HAR11 Hastk1_eq.
        unfold astack_load in *.
        destruct Mem.valid_access_dec; [| inversion HAR11].
        subst astk1.
        rewrite ab_getN_setN_outside; [auto | ].
        right. simpl.
        destruct src; simpl; lia.

      + intros r Hin.
        apply set_add_elim in Hin.
        destruct Hin as [Hin | Hin].
        * subst r.
          apply set_add_intro1; apply set_add_intro2; reflexivity.
        * apply set_add_intro1. apply set_add_intro1.
          apply HSUB; auto.

      + unfold match_regs.
        intro r.
        specialize (REG r).
        destruct REG as (REG1 & REG2 & REG3).
        split.
        * intro Hin.
          destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
          { (**r r = dst *)
            subst r.
            exists i.
            split; repeat abreg_solver.
            rewrite <- HALU. rewrite Hsrc1. simpl; auto.
          }
          destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
          { (**r r = src *)
            subst r.
            exists v_src.
            split; repeat abreg_solver.
          }
          { (**r r <> dst /\ r<> src *)
            assert (Heq: In r (set_union breg_eq ld_set st_set)). {
              apply set_union_elim in Hin.
              destruct Hin as [Hin | Hin].
              - apply set_add_elim in Hin.
                destruct Hin as [Hin | Hin].
                + exfalso; apply Hr_neq_src; auto.
                + apply set_add_elim in Hin.
                  destruct Hin as [Hin | Hin].
                  * exfalso; apply Hr_neq; auto.
                  * apply set_union_intro1; auto.
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
        * split; intro HF.
          { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso; apply HF; clear.
              apply set_union_intro2.
              apply set_add_intro2; auto.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso; apply HF; clear.
              apply set_union_intro1.
              apply set_add_intro2; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
                intro Hin; apply HF.
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_union_intro1.
                  apply set_add_intro1; apply set_add_intro1; auto.
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
              destruct REG3 as (vr3 & Hvr_3 & Hvr_4).
              exists vr3.
              rename HF into Hno_in.
              split; repeat abreg_solver.
            }
          }

      + split; [ init_arm_stack_update1 | ].
        { intros r Hr_callee.
          specialize (STK r Hr_callee).
          destruct STK as (STK1 & STK2).
          split; intro Hin.
          - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              rewrite <- STK1.
              2:{ apply set_union_intro1; auto. }
              subst astk1.
              unfold astack_load.

              destruct Mem.valid_access_dec as [HT | HF]; [| auto].
              assert (Heq: List.length (encode_sval_fragments Cany32
                (Rval (Sreg (ireg_of_breg src)))) = size_chunk_nat Many32). {
                unfold size_chunk_nat; simpl. auto.
              }
              rewrite <- Heq; clear Heq.
              rewrite ab_getN_setN_outside.
              auto.
              simpl.
              clear - Hreg_neq.
              destruct src; destruct dst; simpl; try lia; exfalso; apply Hreg_neq; reflexivity.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              subst astk1.
              unfold astack_load.

              destruct Mem.valid_access_dec as [HT | HF].
              - assert (Heq: List.length (encode_sval_fragments Cany32
                  (Rval (Sreg (ireg_of_breg src)))) = size_chunk_nat Many32). {
                  unfold size_chunk_nat; simpl. auto.
                }
                rewrite <- Heq; clear Heq.
                rewrite ab_getN_setN_same. decode_val_same_breg_solver.
              - valid_access_fail_solver.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: In r (set_union breg_eq ld_set st_set)). {
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_add_elim in Hin.
                  destruct Hin as [Hin | Hin].
                  + exfalso; apply Hr_neq_src; inversion Hin; reflexivity.
                  + apply set_add_elim in Hin.
                    destruct Hin as [Hin | Hin].
                    * exfalso; apply Hr_neq; inversion Hin; reflexivity.
                    * apply set_union_intro1; auto.
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
              clear - Hr_neq_src.
              destruct r; destruct src; simpl; try lia; exfalso; apply Hr_neq_src; reflexivity.
            }
          - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso. clear - Hin.
              apply Hin.
              apply set_union_intro2. apply set_add_intro2; auto.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso. clear - Hin.
              apply Hin.
              apply set_union_intro1. apply set_add_intro2; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
                rename Hin into HF.
                intro Hin; apply HF.
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_union_intro1; apply set_add_intro1; apply set_add_intro1; auto.
                - apply set_union_intro2; apply set_add_intro1; auto.
              }
              specialize (STK2 Heq); clear Heq.
              repeat abreg_solver.
            }
          }
    }

    { simpl.
      rewrite decode_ldr_i_12.
      simpl.

      rewrite HIR12. simpl. rewrite Ptrofs.add_zero_l. rewrite ptr_int_mul_4.

      rewrite Hsrc2.

      rewrite decode_mov_r.
      unfold anextinstr; simpl. repeat abreg_solver_error_prone.

      simpl.
      eexists. exists astk0.
      split; [f_equal |].

      constructor; auto; unfold anextinstr_nf; unfold anextinstr, aundef_flags;
        simpl; repeat abreg_solver.
      + intros r Hin.
        apply set_add_elim in Hin.
        destruct Hin as [Hin | Hin].
        * subst r.
          apply set_add_intro1; apply set_add_intro2; reflexivity.
        * apply set_add_intro1. apply set_add_intro1.
          apply HSUB; auto.

      + unfold match_regs.
        intro r.
        specialize (REG r).
        destruct REG as (REG1 & REG2 & REG3).
        split.
        * intro Hin.
          destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
          { (**r r = dst *)
            subst r.
            exists i.
            split; repeat abreg_solver.
            rewrite <- HALU. rewrite Hsrc1. simpl; auto.
          }
          destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
          { (**r r = src *)
            subst r.
            exists v_src.
            split; repeat abreg_solver.
          }
          { (**r r <> dst /\ r<> src *)
            assert (Heq: In r (set_union breg_eq ld_set st_set)). {
              apply set_union_elim in Hin.
              destruct Hin as [Hin | Hin].
              - apply set_add_elim in Hin.
                destruct Hin as [Hin | Hin].
                + exfalso; apply Hr_neq_src; auto.
                + apply set_add_elim in Hin.
                  destruct Hin as [Hin | Hin].
                  * exfalso; apply Hr_neq; auto.
                  * apply set_union_intro1; auto.
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
        * split; intro HF.
          { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso; apply HF; clear.
              apply set_union_intro2.
              apply set_add_intro2; auto.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso; apply HF; clear.
              apply set_union_intro1.
              apply set_add_intro2; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
                intro Hin; apply HF.
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_union_intro1.
                  apply set_add_intro1; apply set_add_intro1; auto.
                - apply set_union_intro2; apply set_add_intro1; auto.
              }
              specialize (REG2 Heq); clear Heq.

              rename HF into Hno_in. repeat abreg_solver.
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
              destruct REG3 as (vr3 & Hvr_3 & Hvr_4).
              exists vr3.
              rename HF into Hno_in.
              split; repeat abreg_solver.
            }
          }

      + split; [split; auto| ].
        { intros r Hr_callee.
          specialize (STK r Hr_callee).
          destruct STK as (STK1 & STK2).
          split; intro Hin.
          - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              rewrite <- STK1.
              2:{ apply set_union_intro1; auto. }
              auto.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso.
              apply set_mem_arm_callee_save_false in Hcallee.
              apply Hcallee; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: In r (set_union breg_eq ld_set st_set)). {
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_add_elim in Hin.
                  destruct Hin as [Hin | Hin].
                  + exfalso; apply Hr_neq_src; inversion Hin; reflexivity.
                  + apply set_add_elim in Hin.
                    destruct Hin as [Hin | Hin].
                    * exfalso; apply Hr_neq; inversion Hin; reflexivity.
                    * apply set_union_intro1; auto.
                - apply set_add_elim in Hin.
                  destruct Hin as [Hin | Hin].
                  + exfalso; apply Hr_neq; inversion Hin; reflexivity.
                  + apply set_union_intro2; auto.
              }
              specialize (STK1 Heq); clear Heq.
              rewrite <- STK1. auto.
            }
          - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso. clear - Hin.
              apply Hin.
              apply set_union_intro2. apply set_add_intro2; auto.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso. clear - Hin.
              apply Hin.
              apply set_union_intro1. apply set_add_intro2; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
                rename Hin into HF.
                intro Hin; apply HF.
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_union_intro1; apply set_add_intro1; apply set_add_intro1; auto.
                - apply set_union_intro2; apply set_add_intro1; auto.
              }
              specialize (STK2 Heq); clear Heq.
              repeat abreg_solver.
            }
          }
    }
Qed.


Lemma exec_alu32_mov_r_neq_dst_not_in_ld_set:
  forall l2 (dst src: breg) l1 ld_set st_set ld_set2 st_set2
    (rs0 rs1: regset) i jit_blk st_blk m1 ars0 astk0 astkb am
    (HALU : rs0 src = Vint i)
    (Hdst_in : set_mem breg_eq dst ld_set = false)
    (Hl2 : (if set_mem ireg_eq (ireg_of_breg dst) arm_callee_save
       then
        [jit_alu32_thumb_mem_template_jit STR_I_OP (int_of_breg dst) 
           (int_of_ireg IR13) (Int.mul (int_of_breg dst) (Int.repr 4));
        jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg dst) (int_of_ireg IR12)
          (Int.mul (int_of_breg dst) (Int.repr 4))]
       else
        [jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg dst) 
           (int_of_ireg IR12) (Int.mul (int_of_breg dst) (Int.repr 4))]) ++
      (if set_mem breg_eq src (set_add breg_eq dst ld_set)
       then []
       else
        if set_mem ireg_eq (ireg_of_breg src) arm_callee_save
        then
         [jit_alu32_thumb_mem_template_jit STR_I_OP (int_of_breg src) 
            (int_of_ireg IR13) (Int.mul (int_of_breg src) (Int.repr 4));
         jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg src) 
           (int_of_ireg IR12) (Int.mul (int_of_breg src) (Int.repr 4))]
        else
         [jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg src) 
            (int_of_ireg IR12) (Int.mul (int_of_breg src) (Int.repr 4))]) = l2)
    (Hld2 : set_add breg_eq src (set_add breg_eq dst ld_set) = ld_set2)
    (Hst2 : set_add breg_eq dst st_set = st_set2)
    (Hl1 : l2 ++
      [encode_arm32
         (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
            (encode_arm32 (int_of_ireg (ireg_of_breg src))
               (encode_arm32
                  (if Int.lt (int_of_breg dst) (Int.repr 8)
                   then int_of_breg dst
                   else Int.sub (int_of_breg dst) (Int.repr 8)) MOV_R_OP 0 3) 3 4) 7 1) NOP_OP 16
         16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 =
       BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
         (BPregmap.set dst (Vint i) rs0))
    (Hreg_neq : dst <> src),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  intros.
  apply set_mem_complete1 in Hdst_in.
  unfold set_In in Hdst_in.
  unfold jit_alu32_thumb_mem_template_jit in Hl2.

  inversion HST; subst.
  unfold match_regs in REG.

  specialize (REG dst) as REG_DST.
  destruct REG_DST as (REG_DST1 & REG_DST2 & REG_DST3).
  specialize (REG src) as REG_SRC.
  destruct REG_SRC as (REG_SRC1 & REG_SRC2 & REG_SRC3).

  assert (Heq: ~ In dst (set_union breg_eq ld_set st_set)). {
    intro HF.
    apply Hdst_in.
    apply set_union_elim in HF.
    destruct HF as [HF | HF].
    - assumption.
    - apply HSUB.
      assumption.
  }
  specialize (REG_DST2 Heq); clear Heq.

  assert (Heq: ~ In dst st_set). {
    intro HF; apply Hdst_in.
    apply HSUB.
    auto.
  }
  specialize (REG_DST3 Heq); clear Heq.
  destruct REG_DST3 as (v_dst & Hdst1 & Hdst2).

  unfold match_stack in *.
  destruct STK as ((INIT_STK1 & INIT_STK2) & STK).

  destruct set_mem eqn: Hdst_callee.
  {
    apply set_mem_correct1 in Hdst_callee.
    destruct set_mem eqn: Hsrc_in.
    - (**r src in ld_set *)
      rewrite app_nil_r.
      simpl.
      rewrite decode_str_i_13.
      simpl.

      rewrite HIR13. simpl. rewrite Ptrofs.add_zero_l.

      apply set_mem_correct1 in Hsrc_in.
      apply set_add_elim in Hsrc_in.
      destruct Hsrc_in as [HF | Hsrc_in].
      { exfalso; apply Hreg_neq; auto. }
      erewrite aexec_store_ir13; eauto.

      rewrite decode_ldr_i_12.
      remember (setN (encode_sval_fragments Cany32 (Rval (Sreg (ireg_of_breg _))))
         _ astk0) as astk1 eqn: Hastk1_eq.
      simpl.
      unfold anextinstr at 1. repeat abreg_solver_error_prone.
      rewrite HIR12.
      simpl. rewrite Ptrofs.add_zero_l.

      rewrite ptr_int_mul_4.
      rewrite Hdst2.

      rewrite decode_mov_r.

      assert (Hsrc_in_union: In src (set_union breg_eq ld_set st_set)). {
        apply set_union_intro1.
        unfold set_In; auto.
      }

      specialize (REG_SRC1 Hsrc_in_union).
      destruct REG_SRC1 as (v_src & Hsrc1 & Hsrc2).
      simpl.
      unfold anextinstr, aadd; simpl.
      repeat abreg_solver_error_prone.
      rewrite REG_DST2, Hsrc2 in *.

      eexists; eexists.
      split; [f_equal |].
      constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; repeat abreg_solver.
      + clear - HAR11 Hastk1_eq.
        unfold astack_load in *.
        destruct Mem.valid_access_dec; [| inversion HAR11].
        subst astk1.
        rewrite ab_getN_setN_outside; [auto | ].
        right. simpl.
        destruct dst; simpl; lia.

      + intros r Hin.
        apply set_add_elim in Hin.
        destruct Hin as [Hin | Hin].
        * subst r.
          apply set_add_intro1; apply set_add_intro2; auto.
        * specialize (HSUB _ Hin).
          apply set_add_intro1.
          apply set_add_intro1; auto.

      + unfold match_regs.
        intros.
        specialize (REG r).
        destruct REG as (REG1 & REG2 & REG3).
        destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
        { (**r r = dst *)
          subst r.
          split.
          - intro Hin.
            exists i.
            split; repeat abreg_solver. rewrite <- Hsrc1, HALU; f_equal.
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
        destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
        { (**r r = src *)
          subst r.
          specialize (REG1 Hsrc_in_union).
          destruct REG1 as (vr1 & Hvr1 & Hvr2).
          rewrite Hvr1 in Hsrc1.
          injection Hsrc1 as Heq; subst vr1.
          split.
          - intro Hin.
            exists v_src.
            split; repeat abreg_solver.
          - split.
            + intro Hnot_in.
              exfalso.
              apply Hnot_in.
              apply set_union_intro1.
              apply set_add_intro2.
              auto.
            + intros Hnot_in.
              assert (Heq: ~ In src st_set). {
                intro HF; apply Hnot_in. apply set_add_intro1; auto.
              }
              specialize (REG3 Heq); clear Heq.
              destruct REG3 as (vr1 & Hvr3 & Hvr4).
              exists vr1.
              split; repeat abreg_solver.
        }
        { (**r r <> dst /\ r <> src *)
          split.
          - intros.
            assert (Heq: In r (set_union breg_eq ld_set st_set)). {
              apply set_union_elim in H.
              destruct H as [H | H].
              - apply set_add_elim in H.
                destruct H as [H | H]; [exfalso; apply Hr_neq_src; auto |].
                apply set_add_elim in H.
                destruct H as [H | H]; [exfalso; apply Hr_neq; auto |].
                apply set_union_intro1; auto.
              - apply set_add_elim in H.
                destruct H as [H | H]; [exfalso; apply Hr_neq; auto |].
                apply set_union_intro2; auto.
            }
            specialize (REG1 Heq); clear Heq.
            destruct REG1 as (vr1 & Hvr1 & Hvr2).
            exists vr1.
            split; repeat abreg_solver.
          - split.
            + intro HN.
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
                intro HF. apply HN.
                apply set_union_elim in HF.
                destruct HF as [HF | HF].
                - apply set_union_intro1.
                  apply set_add_intro1.
                  apply set_add_intro1; auto.
                - apply set_union_intro2.
                  apply set_add_intro1; auto.
              }
              specialize (REG2 Heq); clear Heq. repeat abreg_solver.
            + intro HN.
              assert (Heq: ~ In r st_set). {
                intro HF. apply HN.
                apply set_add_intro1; auto.
              }
              specialize (REG3 Heq); clear Heq.
              destruct REG3 as (vr1 & Hvr1 & Hvr2).
              exists vr1. split; repeat abreg_solver.
        }

      + split; [init_arm_stack_update1 | ].
        { intros r Hr_callee.
          specialize (STK r Hr_callee).
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
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              rewrite <- STK1.
              2:{ apply set_union_intro1; auto. }
              subst astk1.
              unfold astack_load.

              destruct Mem.valid_access_dec as [HT | HF]; [| auto].
              assert (Heq: List.length (encode_sval_fragments Cany32
                (Rval (Sreg (ireg_of_breg dst)))) = size_chunk_nat Many32). {
                unfold size_chunk_nat; simpl. auto.
              }
              rewrite <- Heq; clear Heq.
              rewrite ab_getN_setN_outside.
              auto.
              simpl.
              clear - Hreg_neq.
              destruct src; destruct dst; simpl; try lia; exfalso; apply Hreg_neq; reflexivity.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: In r (set_union breg_eq ld_set st_set)). {
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_add_elim in Hin.
                  destruct Hin as [Hin | Hin].
                  + exfalso; apply Hr_neq_src; inversion Hin; reflexivity.
                  + apply set_add_elim in Hin.
                    destruct Hin as [Hin | Hin].
                    * exfalso; apply Hr_neq; inversion Hin; reflexivity.
                    * apply set_union_intro1; auto.
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
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso. clear - Hin.
              apply Hin.
              apply set_union_intro1. apply set_add_intro2; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
                rename Hin into HF.
                intro Hin; apply HF.
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_union_intro1; apply set_add_intro1; apply set_add_intro1; auto.
                - apply set_union_intro2; apply set_add_intro1; auto.
              }
              specialize (STK2 Heq); clear Heq. repeat abreg_solver.
            }
        }

  - (**r src not in ld_set *)
    apply set_mem_complete1 in Hsrc_in.

    destruct set_mem eqn: Hcallee.
    {
      apply set_mem_correct1 in Hcallee.
      simpl.
      rewrite decode_str_i_13.
      simpl.

      rewrite HIR13. simpl. rewrite Ptrofs.add_zero_l.

      assert (Heq: ~In src ld_set). {
        intro HF; apply Hsrc_in.
        apply set_add_intro1; auto.
      }
      clear Hsrc_in; rename Heq into Hsrc_in.

      assert (Heq: ~ In src st_set). {
        intro HF; apply Hsrc_in.
        apply HSUB.
        auto.
      }
      specialize (REG_SRC3 Heq); clear Heq.
      destruct REG_SRC3 as (v_src & Hsrc1 & Hsrc2).

      erewrite aexec_store_ir13; eauto.

      rewrite decode_ldr_i_12.
      remember (setN (encode_sval_fragments Cany32 (Rval (Sreg (ireg_of_breg _))))
       _ astk0) as astk1 eqn: Hastk1_eq.
      simpl.
      unfold anextinstr at 1. repeat abreg_solver_error_prone.
      rewrite HIR12.
      simpl. rewrite Ptrofs.add_zero_l.

      rewrite ptr_int_mul_4.

      rewrite Hdst2.
      rewrite decode_mov_r.
      unfold anextinstr; simpl.
      rewrite decode_str_i_13.
      simpl. repeat abreg_solver_error_prone.
      rewrite HIR13. simpl. rewrite Ptrofs.add_zero_l.

      assert (Heq: ~ In src (set_union breg_eq ld_set st_set)). {
        intro HF; apply Hsrc_in.
        apply set_union_elim in HF.
        destruct HF as [HF | HF].
        - assumption.
        - apply HSUB.
          assumption.
      }
      specialize (REG_SRC2 Heq); clear Heq.

      remember (((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize)) # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
      (aoffset_ptr ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize)) # (ireg_of_breg dst) <- (Cval (Vint v_dst)) PC)
         wsize)) as asrt eqn: Hasrt_eq.

      erewrite aexec_store_ir13; eauto.
      2:{ subst asrt. repeat abreg_solver_error_prone. assumption. }

      rewrite decode_ldr_i_12.
      remember (setN (encode_sval_fragments Cany32 (Rval (Sreg (ireg_of_breg _))))
       _ astk1) as astk2 eqn: Hastk2_eq.
      simpl.
      unfold anextinstr at 1.
      subst asrt. repeat abreg_solver_error_prone.
      rewrite HIR12.
      simpl. rewrite Ptrofs.add_zero_l.

      rewrite ptr_int_mul_4.

      rewrite Hsrc2.

      simpl.
      eexists. exists astk2.
      split; [f_equal |].

      constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; simpl; repeat abreg_solver.
      + clear - HAR11 Hastk1_eq Hastk2_eq.
        unfold astack_load in *.
        destruct Mem.valid_access_dec; [| inversion HAR11].
        subst astk1 astk2.
        rewrite ab_getN_setN_outside; [auto | ].
        * rewrite ab_getN_setN_outside; [auto | ].
          right. simpl.
          destruct dst; simpl; lia.
        * right. simpl.
          destruct src; simpl; lia.

      + intros r Hin.
        apply set_add_elim in Hin.
        destruct Hin as [Hin | Hin].
        * subst r.
          apply set_add_intro1; apply set_add_intro2; reflexivity.
        * apply set_add_intro1. apply set_add_intro1.
          apply HSUB; auto.

      + unfold match_regs.
        intro r.
        specialize (REG r).
        destruct REG as (REG1 & REG2 & REG3).
        split.
        * intro Hin.
          destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
          { (**r r = dst *)
            subst r.
            exists i.
            split; repeat abreg_solver.
            rewrite <- HALU. rewrite Hsrc1. simpl; auto.
          }
          destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
          { (**r r = src *)
            subst r.
            exists v_src.
            split; repeat abreg_solver.
          }
          { (**r r <> dst /\ r<> src *)
            assert (Heq: In r (set_union breg_eq ld_set st_set)). {
              apply set_union_elim in Hin.
              destruct Hin as [Hin | Hin].
              - apply set_add_elim in Hin.
                destruct Hin as [Hin | Hin].
                + exfalso; apply Hr_neq_src; auto.
                + apply set_add_elim in Hin.
                  destruct Hin as [Hin | Hin].
                  * exfalso; apply Hr_neq; auto.
                  * apply set_union_intro1; auto.
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
        * split; intro HF.
          { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso; apply HF; clear.
              apply set_union_intro2.
              apply set_add_intro2; auto.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso; apply HF; clear.
              apply set_union_intro1.
              apply set_add_intro2; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
                intro Hin; apply HF.
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_union_intro1.
                  apply set_add_intro1; apply set_add_intro1; auto.
                - apply set_union_intro2; apply set_add_intro1; auto.
              }
              specialize (REG2 Heq); clear Heq.

              rename HF into Hno_in. repeat abreg_solver.
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
              destruct REG3 as (vr3 & Hvr_3 & Hvr_4).
              exists vr3.
              rename HF into Hno_in.
              split; repeat abreg_solver.
            }
          }

      + split.
        { unfold init_arm_stack.
          split; [| auto].
          rewrite <- INIT_STK1.
          unfold astack_load.
          destruct Mem.valid_access_dec; [|reflexivity].
          subst astk1 astk2.
          rewrite ab_getN_setN_outside;
            [ rewrite ab_getN_setN_outside; [f_equal | ] | ].
          - simpl; left;
            clear - Hdst_callee; apply arm_callee_save_reg_ge4; auto.
          - simpl.
            left.
            clear - Hcallee. apply arm_callee_save_reg_ge4; auto.
        }
        { intros r Hr_callee.
          specialize (STK r Hr_callee).
          destruct STK as (STK1 & STK2).
          split; intro Hin.
          - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              subst astk1 astk2.
              unfold astack_load.

              destruct Mem.valid_access_dec as [HT | HF].
              - assert (Heq: List.length (encode_sval_fragments Cany32
                  (Rval (Sreg (ireg_of_breg dst)))) = size_chunk_nat Many32). {
                  unfold size_chunk_nat; simpl. auto.
                }
                rewrite <- Heq; clear Heq.
                rewrite ab_getN_setN_outside.
                + rewrite ab_getN_setN_same. decode_val_same_breg_solver.
                + simpl.
                  clear - Hreg_neq.
                  destruct src; destruct dst; simpl; try lia; exfalso; apply Hreg_neq; reflexivity.
              - valid_access_fail_solver.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              subst astk1 astk2.
              unfold astack_load.

              destruct Mem.valid_access_dec as [HT | HF].
              - assert (Heq: List.length (encode_sval_fragments Cany32
                  (Rval (Sreg (ireg_of_breg src)))) = size_chunk_nat Many32). {
                  unfold size_chunk_nat; simpl. auto.
                }
                rewrite <- Heq; clear Heq.
                rewrite ab_getN_setN_same. decode_val_same_breg_solver.
              - valid_access_fail_solver.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: In r (set_union breg_eq ld_set st_set)). {
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_add_elim in Hin.
                  destruct Hin as [Hin | Hin].
                  + exfalso; apply Hr_neq_src; inversion Hin; reflexivity.
                  + apply set_add_elim in Hin.
                    destruct Hin as [Hin | Hin].
                    * exfalso; apply Hr_neq; inversion Hin; reflexivity.
                    * apply set_union_intro1; auto.
                - apply set_add_elim in Hin.
                  destruct Hin as [Hin | Hin].
                  + exfalso; apply Hr_neq; inversion Hin; reflexivity.
                  + apply set_union_intro2; auto.
              }
              specialize (STK1 Heq); clear Heq.
              subst astk1 astk2.
              rewrite <- STK1.
              unfold astack_load.
              destruct Mem.valid_access_dec; [| auto].
              rewrite ab_getN_setN_outside.
              - rewrite ab_getN_setN_outside.
                + f_equal.
                + simpl.
                  clear - Hr_neq.
                  destruct r; destruct dst; simpl; try lia; exfalso; apply Hr_neq; reflexivity.
              - simpl.
                clear - Hr_neq_src.
                destruct r; destruct src; simpl; try lia; exfalso; apply Hr_neq_src; reflexivity.
            }
          - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso. clear - Hin.
              apply Hin.
              apply set_union_intro2. apply set_add_intro2; auto.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso. clear - Hin.
              apply Hin.
              apply set_union_intro1. apply set_add_intro2; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
                rename Hin into HF.
                intro Hin; apply HF.
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_union_intro1; apply set_add_intro1; apply set_add_intro1; auto.
                - apply set_union_intro2; apply set_add_intro1; auto.
              }
              specialize (STK2 Heq); clear Heq. repeat abreg_solver.
            }
        }
    }

    { simpl.
      rewrite decode_str_i_13.
      simpl.

      rewrite HIR13. simpl. rewrite Ptrofs.add_zero_l.

      assert (Heq: ~In src ld_set). {
        intro HF; apply Hsrc_in.
        apply set_add_intro1; auto.
      }
      clear Hsrc_in; rename Heq into Hsrc_in.

      erewrite aexec_store_ir13; eauto.

      rewrite decode_ldr_i_12.

      remember (setN (encode_sval_fragments Cany32 (Rval (Sreg (ireg_of_breg _))))
       _ astk0) as astk1 eqn: Hastk1_eq.
      simpl.
      unfold anextinstr at 1. repeat abreg_solver_error_prone.
      rewrite HIR12.
      simpl. rewrite Ptrofs.add_zero_l.

      rewrite ptr_int_mul_4.

      rewrite Hdst2.

      rewrite decode_ldr_i_12.
      simpl.
      unfold aexec_load.
      assert (Heq: (anextinstr true (anextinstr true ars0) #
      (ireg_of_breg dst) <- (Cval (Vint v_dst)) IR12) = ars0 IR12). {
        unfold anextinstr. repeat abreg_solver.
      }
      rewrite Heq; clear Heq.
      rewrite HIR12; simpl.
      rewrite Ptrofs.add_zero_l.
      rewrite ptr_int_mul_4.

      assert (Heq: ~ In src st_set). {
        intro HF; apply Hsrc_in.
        apply HSUB.
        auto.
      }
      specialize (REG_SRC3 Heq); clear Heq.
      destruct REG_SRC3 as (v_src & Hsrc1 & Hsrc2).
      rewrite Hsrc2.

      rewrite decode_mov_r.
      unfold anextinstr; simpl. repeat abreg_solver_error_prone.
      simpl.

      eexists. exists astk1.
      split; [f_equal |].

      constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; simpl; repeat abreg_solver.
      + clear - HAR11 Hastk1_eq.
        unfold astack_load in *.
        destruct Mem.valid_access_dec; [| inversion HAR11].
        subst astk1.
        rewrite ab_getN_setN_outside; [auto | ].
        right. simpl.
        destruct dst; simpl; lia.

      + intros r Hin.
        apply set_add_elim in Hin.
        destruct Hin as [Hin | Hin].
        * subst r.
          apply set_add_intro1; apply set_add_intro2; reflexivity.
        * apply set_add_intro1. apply set_add_intro1.
          apply HSUB; auto.

      + unfold match_regs.
        intro r.
        specialize (REG r).
        destruct REG as (REG1 & REG2 & REG3).
        split.
        * intro Hin.
          destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
          { (**r r = dst *)
            subst r.
            exists i.
            split; repeat abreg_solver.
            rewrite <- HALU. rewrite Hsrc1. simpl; auto.
          }
          destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
          { (**r r = src *)
            subst r.
            exists v_src.
            split; repeat abreg_solver.
          }
          { (**r r <> dst /\ r<> src *)
            assert (Heq: In r (set_union breg_eq ld_set st_set)). {
              apply set_union_elim in Hin.
              destruct Hin as [Hin | Hin].
              - apply set_add_elim in Hin.
                destruct Hin as [Hin | Hin].
                + exfalso; apply Hr_neq_src; auto.
                + apply set_add_elim in Hin.
                  destruct Hin as [Hin | Hin].
                  * exfalso; apply Hr_neq; auto.
                  * apply set_union_intro1; auto.
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
        * split; intro HF.
          { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso; apply HF; clear.
              apply set_union_intro2.
              apply set_add_intro2; auto.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso; apply HF; clear.
              apply set_union_intro1.
              apply set_add_intro2; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
                intro Hin; apply HF.
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_union_intro1.
                  apply set_add_intro1; apply set_add_intro1; auto.
                - apply set_union_intro2; apply set_add_intro1; auto.
              }
              specialize (REG2 Heq); clear Heq.

              rename HF into Hno_in. repeat abreg_solver.
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
              destruct REG3 as (vr3 & Hvr_3 & Hvr_4).
              exists vr3.
              rename HF into Hno_in.
              split; repeat abreg_solver.
            }
          }

      + split; [init_arm_stack_update1 | ].
        { intros r Hr_callee.
          specialize (STK r Hr_callee).
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
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso.
              clear - Hcallee Hr_callee.
              apply set_mem_arm_callee_save_false in Hcallee.
              apply Hcallee; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: In r (set_union breg_eq ld_set st_set)). {
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_add_elim in Hin.
                  destruct Hin as [Hin | Hin].
                  + exfalso; apply Hr_neq_src; inversion Hin; reflexivity.
                  + apply set_add_elim in Hin.
                    destruct Hin as [Hin | Hin].
                    * exfalso; apply Hr_neq; inversion Hin; reflexivity.
                    * apply set_union_intro1; auto.
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
              rewrite ab_getN_setN_outside; [auto | ].
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
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso. clear - Hin.
              apply Hin.
              apply set_union_intro1. apply set_add_intro2; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
                rename Hin into HF.
                intro Hin; apply HF.
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_union_intro1; apply set_add_intro1; apply set_add_intro1; auto.
                - apply set_union_intro2; apply set_add_intro1; auto.
              }
              specialize (STK2 Heq); clear Heq. repeat abreg_solver.
            }
        }
      }
  }

  {
    destruct (set_mem breg_eq src (set_add breg_eq dst ld_set)) eqn: Hsrc_in.
    - (**r src in ld_set *)
      simpl.
      rewrite decode_ldr_i_12.
      simpl.

      rewrite HIR12. simpl. rewrite Ptrofs.add_zero_l.

      apply set_mem_correct1 in Hsrc_in.
      apply set_add_elim in Hsrc_in.
      destruct Hsrc_in as [HF | Hsrc_in].
      { exfalso; apply Hreg_neq; auto. }

      rewrite ptr_int_mul_4.

      rewrite Hdst2.
      rewrite decode_mov_r.

      assert (Hsrc_in_union: In src (set_union breg_eq ld_set st_set)). {
        apply set_union_intro1.
        unfold set_In; auto.
      }

      specialize (REG_SRC1 Hsrc_in_union).
      destruct REG_SRC1 as (v_src & Hsrc1 & Hsrc2).
      simpl.
      unfold anextinstr, aadd; simpl. repeat abreg_solver_error_prone.
      rewrite REG_DST2, Hsrc2 in *.

      eexists; eexists.
      split; [f_equal |].
      constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; repeat abreg_solver.

      + intros r Hin.
        apply set_add_elim in Hin.
        destruct Hin as [Hin | Hin].
        * subst r.
          apply set_add_intro1; apply set_add_intro2; auto.
        * specialize (HSUB _ Hin).
          apply set_add_intro1.
          apply set_add_intro1; auto.

      + unfold match_regs.
        intros.
        specialize (REG r).
        destruct REG as (REG1 & REG2 & REG3).
        destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
        { (**r r = dst *)
          subst r.
          split.
          - intro Hin.
            exists i.
            split; repeat abreg_solver. rewrite <- HALU, Hsrc1.
            simpl; auto.
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
        destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
        { (**r r = src *)
          subst r.
          specialize (REG1 Hsrc_in_union).
          destruct REG1 as (vr1 & Hvr1 & Hvr2).
          rewrite Hvr1 in Hsrc1.
          injection Hsrc1 as Heq; subst vr1.
          split.
          - intro Hin.
            exists v_src.
            split; repeat abreg_solver.
          - split.
            + intro Hnot_in.
              exfalso.
              apply Hnot_in.
              apply set_union_intro1.
              apply set_add_intro2.
              auto.
            + intros Hnot_in.
              assert (Heq: ~ In src st_set). {
                intro HF; apply Hnot_in. apply set_add_intro1; auto.
              }
              specialize (REG3 Heq); clear Heq.
              destruct REG3 as (vr1 & Hvr3 & Hvr4).
              exists vr1.
              split; repeat abreg_solver.
        }
        { (**r r <> dst /\ r <> src *)
          split.
          - intros.
            assert (Heq: In r (set_union breg_eq ld_set st_set)). {
              apply set_union_elim in H.
              destruct H as [H | H].
              - apply set_add_elim in H.
                destruct H as [H | H]; [exfalso; apply Hr_neq_src; auto |].
                apply set_add_elim in H.
                destruct H as [H | H]; [exfalso; apply Hr_neq; auto |].
                apply set_union_intro1; auto.
              - apply set_add_elim in H.
                destruct H as [H | H]; [exfalso; apply Hr_neq; auto |].
                apply set_union_intro2; auto.
            }
            specialize (REG1 Heq); clear Heq.
            destruct REG1 as (vr1 & Hvr1 & Hvr2).
            exists vr1. split; repeat abreg_solver.
          - split.
            + intro HN.
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
                intro HF. apply HN.
                apply set_union_elim in HF.
                destruct HF as [HF | HF].
                - apply set_union_intro1.
                  apply set_add_intro1.
                  apply set_add_intro1; auto.
                - apply set_union_intro2.
                  apply set_add_intro1; auto.
              }
              specialize (REG2 Heq); clear Heq. repeat abreg_solver.
            + intro HN.
              assert (Heq: ~ In r st_set). {
                intro HF. apply HN.
                apply set_add_intro1; auto.
              }
              specialize (REG3 Heq); clear Heq.
              destruct REG3 as (vr1 & Hvr1 & Hvr2).
              exists vr1. split; repeat abreg_solver.
        }

      + split; [split; auto |].

        { intros r Hr_callee.
          specialize (STK r Hr_callee).
          destruct STK as (STK1 & STK2).
          split; intro Hin.
          - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso.
              apply set_mem_arm_callee_save_false in Hdst_callee.
              apply Hdst_callee; auto.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              apply STK1.
              apply set_union_intro1; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: In r (set_union breg_eq ld_set st_set)). {
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_add_elim in Hin.
                  destruct Hin as [Hin | Hin].
                  + exfalso; apply Hr_neq_src; inversion Hin; reflexivity.
                  + apply set_add_elim in Hin.
                    destruct Hin as [Hin | Hin].
                    * exfalso; apply Hr_neq; inversion Hin; reflexivity.
                    * apply set_union_intro1; auto.
                - apply set_add_elim in Hin.
                  destruct Hin as [Hin | Hin].
                  + exfalso; apply Hr_neq; inversion Hin; reflexivity.
                  + apply set_union_intro2; auto.
              }
              specialize (STK1 Heq); clear Heq.
              apply STK1.
            }
          - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso. clear - Hin.
              apply Hin.
              apply set_union_intro2. apply set_add_intro2; auto.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso. clear - Hin.
              apply Hin.
              apply set_union_intro1. apply set_add_intro2; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
                rename Hin into HF.
                intro Hin; apply HF.
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_union_intro1; apply set_add_intro1; apply set_add_intro1; auto.
                - apply set_union_intro2; apply set_add_intro1; auto.
              }
              specialize (STK2 Heq); clear Heq. repeat abreg_solver.
            }
        }

  - (**r src not in ld_set *)
    apply set_mem_complete1 in Hsrc_in.

    destruct (set_mem ireg_eq (ireg_of_breg src) arm_callee_save) eqn: Hcallee.
    {
      apply set_mem_correct1 in Hcallee.
      simpl.
      rewrite decode_ldr_i_12.
      simpl.

      rewrite HIR12. simpl. rewrite Ptrofs.add_zero_l.

      assert (Heq: ~In src ld_set). {
        intro HF; apply Hsrc_in.
        apply set_add_intro1; auto.
      }
      clear Hsrc_in; rename Heq into Hsrc_in.
      rewrite ptr_int_mul_4.
      rewrite Hdst2.

      rewrite decode_str_i_13.
      simpl.

      assert (Heq: (anextinstr true ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst)) IR13) = ars0 IR13). {
        unfold anextinstr. repeat abreg_solver.
      }
      rewrite Heq; clear Heq.
      rewrite HIR13. simpl. rewrite Ptrofs.add_zero_l.

      assert (Heq: ~ In src (set_union breg_eq ld_set st_set)). {
        intro HF; apply Hsrc_in.
        apply set_union_elim in HF.
        destruct HF as [HF | HF].
        - assumption.
        - apply HSUB.
          assumption.
      }
      specialize (REG_SRC2 Heq); clear Heq.

      erewrite aexec_store_ir13; eauto.
      2:{ unfold anextinstr; simpl. repeat abreg_solver_error_prone. assumption. }

      rewrite decode_ldr_i_12.
      remember (setN (encode_sval_fragments Cany32 (Rval (Sreg (ireg_of_breg _))))
       _ astk0) as astk1 eqn: Hastk1_eq.
      simpl.
      unfold anextinstr at 1. repeat abreg_solver_error_prone.

      assert (Heq: (anextinstr true ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst)) IR12) = ars0 IR12). {
        unfold anextinstr. repeat abreg_solver.
      }
      rewrite Heq; clear Heq.
      rewrite HIR12.
      simpl. rewrite Ptrofs.add_zero_l.

      assert (Heq: ~ In src st_set). {
        intro HF; apply Hsrc_in.
        apply HSUB.
        auto.
      }
      specialize (REG_SRC3 Heq); clear Heq.
      destruct REG_SRC3 as (v_src & Hsrc1 & Hsrc2).

      rewrite ptr_int_mul_4.

      rewrite Hsrc2.
      rewrite decode_mov_r.
      unfold anextinstr; simpl. repeat abreg_solver_error_prone.

      simpl.
      eexists. exists astk1.
      split; [f_equal |].

      constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; simpl; repeat abreg_solver.
      + clear - HAR11 Hastk1_eq.
        unfold astack_load in *.
        destruct Mem.valid_access_dec; [| inversion HAR11].
        subst astk1.
        rewrite ab_getN_setN_outside; [auto | ].
        right. simpl.
        destruct src; simpl; lia.

      + intros r Hin.
        apply set_add_elim in Hin.
        destruct Hin as [Hin | Hin].
        * subst r.
          apply set_add_intro1; apply set_add_intro2; reflexivity.
        * apply set_add_intro1. apply set_add_intro1.
          apply HSUB; auto.

      + unfold match_regs.
        intro r.
        specialize (REG r).
        destruct REG as (REG1 & REG2 & REG3).
        split.
        * intro Hin.
          destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
          { (**r r = dst *)
            subst r.
            exists i.
            split; repeat abreg_solver.
            rewrite <- HALU. rewrite Hsrc1. simpl; auto.
          }
          destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
          { (**r r = src *)
            subst r.
            exists v_src.
            split; repeat abreg_solver.
          }
          { (**r r <> dst /\ r<> src *)
            assert (Heq: In r (set_union breg_eq ld_set st_set)). {
              apply set_union_elim in Hin.
              destruct Hin as [Hin | Hin].
              - apply set_add_elim in Hin.
                destruct Hin as [Hin | Hin].
                + exfalso; apply Hr_neq_src; auto.
                + apply set_add_elim in Hin.
                  destruct Hin as [Hin | Hin].
                  * exfalso; apply Hr_neq; auto.
                  * apply set_union_intro1; auto.
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
        * split; intro HF.
          { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso; apply HF; clear.
              apply set_union_intro2.
              apply set_add_intro2; auto.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso; apply HF; clear.
              apply set_union_intro1.
              apply set_add_intro2; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
                intro Hin; apply HF.
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_union_intro1.
                  apply set_add_intro1; apply set_add_intro1; auto.
                - apply set_union_intro2; apply set_add_intro1; auto.
              }
              specialize (REG2 Heq); clear Heq.

              rename HF into Hno_in. repeat abreg_solver.
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
              destruct REG3 as (vr3 & Hvr_3 & Hvr_4).
              exists vr3.
              rename HF into Hno_in.
              split; repeat abreg_solver.
            }
          }

      + split; [init_arm_stack_update1 | ].
        { intros r Hr_callee.
          specialize (STK r Hr_callee).
          destruct STK as (STK1 & STK2).
          split; intro Hin.
          - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.

              exfalso.
              apply set_mem_arm_callee_save_false in Hdst_callee.
              apply Hdst_callee; auto.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              subst astk1.
              unfold astack_load.

              destruct Mem.valid_access_dec as [HT | HF].
              - assert (Heq: List.length (encode_sval_fragments Cany32
                  (Rval (Sreg (ireg_of_breg src)))) = size_chunk_nat Many32). {
                  unfold size_chunk_nat; simpl. auto.
                }
                rewrite <- Heq; clear Heq.
                rewrite ab_getN_setN_same. decode_val_same_breg_solver.
              - valid_access_fail_solver.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: In r (set_union breg_eq ld_set st_set)). {
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_add_elim in Hin.
                  destruct Hin as [Hin | Hin].
                  + exfalso; apply Hr_neq_src; inversion Hin; reflexivity.
                  + apply set_add_elim in Hin.
                    destruct Hin as [Hin | Hin].
                    * exfalso; apply Hr_neq; inversion Hin; reflexivity.
                    * apply set_union_intro1; auto.
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
              rewrite ab_getN_setN_outside; auto.
              simpl.
              clear - Hr_neq_src.
              destruct r; destruct src; simpl; try lia; exfalso; apply Hr_neq_src; reflexivity.
            }
          - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso. clear - Hin.
              apply Hin.
              apply set_union_intro2. apply set_add_intro2; auto.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso. clear - Hin.
              apply Hin.
              apply set_union_intro1. apply set_add_intro2; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
                rename Hin into HF.
                intro Hin; apply HF.
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_union_intro1; apply set_add_intro1; apply set_add_intro1; auto.
                - apply set_union_intro2; apply set_add_intro1; auto.
              }
              specialize (STK2 Heq); clear Heq. repeat abreg_solver.
            }
        }
    }

    { simpl.
      rewrite decode_ldr_i_12.
      simpl.

      rewrite HIR12. simpl. rewrite Ptrofs.add_zero_l.

      assert (Heq: ~In src ld_set). {
        intro HF; apply Hsrc_in.
        apply set_add_intro1; auto.
      }
      clear Hsrc_in; rename Heq into Hsrc_in.
      rewrite ptr_int_mul_4.

      rewrite decode_ldr_i_12.
      rewrite Hdst2.
      unfold anextinstr at 1; simpl. repeat abreg_solver_error_prone.
      rewrite HIR12.
      simpl. rewrite Ptrofs.add_zero_l.
      rewrite ptr_int_mul_4.

      assert (Heq: ~ In src st_set). {
        intro HF; apply Hsrc_in.
        apply HSUB; auto.
      }
      specialize (REG_SRC3 Heq); clear Heq.
      destruct REG_SRC3 as (v_src & Hsrc1 & Hsrc2).

      rewrite Hsrc2.

      rewrite decode_mov_r.
      unfold anextinstr; simpl. repeat abreg_solver_error_prone.
      simpl.

      eexists. exists astk0.
      split; [f_equal |].

      constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; simpl; repeat abreg_solver.
      + intros r Hin.
        apply set_add_elim in Hin.
        destruct Hin as [Hin | Hin].
        * subst r.
          apply set_add_intro1; apply set_add_intro2; reflexivity.
        * apply set_add_intro1. apply set_add_intro1.
          apply HSUB; auto.

      + unfold match_regs.
        intro r.
        specialize (REG r).
        destruct REG as (REG1 & REG2 & REG3).
        split.
        * intro Hin.
          destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
          { (**r r = dst *)
            subst r.
            exists i.
            split; repeat abreg_solver.
            rewrite <- HALU. rewrite Hsrc1. simpl; auto.
          }
          destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
          { (**r r = src *)
            subst r.
            exists v_src.
            split; repeat abreg_solver.
          }
          { (**r r <> dst /\ r<> src *)
            assert (Heq: In r (set_union breg_eq ld_set st_set)). {
              apply set_union_elim in Hin.
              destruct Hin as [Hin | Hin].
              - apply set_add_elim in Hin.
                destruct Hin as [Hin | Hin].
                + exfalso; apply Hr_neq_src; auto.
                + apply set_add_elim in Hin.
                  destruct Hin as [Hin | Hin].
                  * exfalso; apply Hr_neq; auto.
                  * apply set_union_intro1; auto.
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
        * split; intro HF.
          { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso; apply HF; clear.
              apply set_union_intro2.
              apply set_add_intro2; auto.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso; apply HF; clear.
              apply set_union_intro1.
              apply set_add_intro2; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
                intro Hin; apply HF.
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_union_intro1.
                  apply set_add_intro1; apply set_add_intro1; auto.
                - apply set_union_intro2; apply set_add_intro1; auto.
              }
              specialize (REG2 Heq); clear Heq.

              rename HF into Hno_in. repeat abreg_solver.
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
              destruct REG3 as (vr3 & Hvr_3 & Hvr_4).
              exists vr3.
              rename HF into Hno_in.
              split; repeat abreg_solver.
            }
          }

      + split; [split; auto |].
        { intros r Hr_callee.
          specialize (STK r Hr_callee).
          destruct STK as (STK1 & STK2).
          split; intro Hin.
          - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso.
              apply set_mem_arm_callee_save_false in Hdst_callee.
              apply Hdst_callee; auto.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso.
              clear - Hcallee Hr_callee.
              apply set_mem_arm_callee_save_false in Hcallee.
              apply Hcallee; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: In r (set_union breg_eq ld_set st_set)). {
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_add_elim in Hin.
                  destruct Hin as [Hin | Hin].
                  + exfalso; apply Hr_neq_src; inversion Hin; reflexivity.
                  + apply set_add_elim in Hin.
                    destruct Hin as [Hin | Hin].
                    * exfalso; apply Hr_neq; inversion Hin; reflexivity.
                    * apply set_union_intro1; auto.
                - apply set_add_elim in Hin.
                  destruct Hin as [Hin | Hin].
                  + exfalso; apply Hr_neq; inversion Hin; reflexivity.
                  + apply set_union_intro2; auto.
              }
              specialize (STK1 Heq); clear Heq.
              rewrite <- STK1. auto.
            }
          - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso. clear - Hin.
              apply Hin.
              apply set_union_intro2. apply set_add_intro2; auto.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso. clear - Hin.
              apply Hin.
              apply set_union_intro1. apply set_add_intro2; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
                rename Hin into HF.
                intro Hin; apply HF.
                apply set_union_elim in Hin.
                destruct Hin as [Hin | Hin].
                - apply set_union_intro1; apply set_add_intro1; apply set_add_intro1; auto.
                - apply set_union_intro2; apply set_add_intro1; auto.
              }
              specialize (STK2 Heq); clear Heq. repeat abreg_solver.
            }
        }
      }
  }
Qed.

Lemma exec_alu32_mov_r:
  forall (rs0 rs1: regset) (dst src: breg) i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : rs0 src = Vint i)
    (Hsave : jit_call_save_reg dst src ld_set st_set = (l2, ld_set2, st_set2))
    (HREG_NEQ : dst <> src)
    (Hl1 : l2 ++
      [encode_arm32
         (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
            (encode_arm32 (int_of_ireg (ireg_of_breg src))
               (encode_arm32
                  (if Int.lt (int_of_breg dst) (Int.repr 8)
                   then int_of_breg dst
                   else Int.sub (int_of_breg dst) (Int.repr 8)) MOV_R_OP 0 3) 3 4) 7 1) NOP_OP 16
         16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  intros.
  unfold jit_call_save_reg in Hsave.
  injection Hsave as Hl2 Hld2 Hst2.
  unfold jit_call_save_add in Hl2.
  destruct set_mem eqn: Hdst_in in Hl2.
  + (**r dst in ld *)
    rewrite app_nil_l in Hl2.
    eapply exec_alu32_mov_r_neq_dst_in_ld_set; eauto.
  + (**r dst not in ld *)
    eapply exec_alu32_mov_r_neq_dst_not_in_ld_set; eauto.
Qed.