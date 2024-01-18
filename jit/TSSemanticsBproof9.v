From compcert.lib Require Import Integers Coqlib Maps.
From compcert.common Require Import AST Values Memory.
From compcert.arm Require Import AsmSyntax ABinSem BinDecode BinSyntax.

From bpf.rbpf32 Require Import TSSyntax JITConfig.
From bpf.jit Require Import Arm32Reg ThumbInsOp ThumbJIT WholeCompiler.
From bpf.jit Require Import ThumbJITLtac ABMemory TSSemanticsB ThumbJITProofLemma0 TSSemanticsBproofdef.
From bpf.jit Require Import BitfieldLemma ThumbDecodeEncodeALU ThumbDecodeEncodeALU0 ThumbDecodeEncodeMEM.
From Coq Require Import ZArith Lia List ListSet.

Open Scope nat_scope.
Open Scope asm.
Import ListNotations.

Lemma exec_alu32_sub_i_neq_dst_in_ld_set:
  forall (dst: breg) si l1 ld_set st_set ld_set2 st_set2
    (rs0 rs1: regset) i jit_blk st_blk m1 ars0 astk0 astkb am
    (HALU : Val.sub (rs0 dst) (Vint si) = Vint i)
    (Hdst_in : set_mem breg_eq dst (set_union breg_eq ld_set st_set) = true)
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true)
    (Hld2 : set_add breg_eq dst ld_set = ld_set2)
    (Hst2 : set_add breg_eq dst st_set = st_set2)
    (Hl1 : [encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) SUB_I_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 =
       BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
         (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  intros.

  inversion HST; subst.
  unfold match_regs in REG.
  specialize (REG dst) as REG_DST.
  apply set_mem_correct1 in Hdst_in.
  unfold set_In in Hdst_in.
  destruct REG_DST as (REG_DST1 & REG_DST2 & REG_DST3).

  specialize (REG_DST1 Hdst_in).
  destruct REG_DST1 as (v_dst & Hdst1 & Hdst2).

  unfold match_stack in *.
  destruct STK as ((INIT_STK1 & INIT_STK2) & STK).

  simpl.
  rewrite decode_sub_i; auto.
  simpl.

  rewrite Hdst2 in *.
  simpl.
  rewrite Hdst1 in HALU.
  simpl in HALU.
  injection HALU as Heq; subst i.
  eexists; eexists.
  split; [f_equal |].
  constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; repeat abreg_solver.
  + intros r Hin.
    apply set_add_elim in Hin.
    destruct Hin as [Hin | Hin].
    * subst r.
      apply set_add_intro2; auto.
    * specialize (HSUB _ Hin).
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
        exists (Int.sub v_dst si).
        split; repeat abreg_solver.
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
          assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
            intro HF. apply HN.
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
          auto.
        + apply set_union_intro1; auto.
      - apply set_add_elim in H0.
        destruct H0 as [H0 | H0].
        + subst r.
          auto.
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
          apply set_add_intro1; auto.
        + apply set_union_intro2.
          apply set_add_intro1; auto.
    }
Qed.

Lemma exec_alu32_sub_i_neq_dst_not_in_ld_set:
  forall (dst: breg) si l1 l2 ld_set st_set ld_set2 st_set2
    (rs0 rs1: regset) i jit_blk st_blk m1 ars0 astk0 astkb am
    (HALU : Val.sub (rs0 dst) (Vint si) = Vint i)
    (Hdst_in : set_mem breg_eq dst (set_union breg_eq ld_set st_set) = false)
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true)
    (Hld2 : set_add breg_eq dst ld_set = ld_set2)
    (Hst2 : set_add breg_eq dst st_set = st_set2)
    (Hl2 : (if set_mem ireg_eq (ireg_of_breg dst) arm_callee_save
       then
        [jit_alu32_thumb_mem_template_jit STR_I_OP (int_of_breg dst) (int_of_ireg IR13)
           (Int.mul (int_of_breg dst) (Int.repr 4));
        jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg dst) (int_of_ireg IR12)
          (Int.mul (int_of_breg dst) (Int.repr 4))]
       else
        [jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg dst) (int_of_ireg IR12)
           (Int.mul (int_of_breg dst) (Int.repr 4))]) = l2)
    (Hl1 : l2 ++
      [encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) SUB_I_OP 0 4) 16 16] =
      l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 =
       BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
         (BPregmap.set dst (Vint i) rs0)),
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

  specialize (REG_DST2 Hdst_in).

  assert (Heq: ~ In dst st_set). {
    intro HF; apply Hdst_in.
    apply set_union_intro2; auto.
  }
  specialize (REG_DST3 Heq); clear Heq.
  destruct REG_DST3 as (v_dst & Hdst1 & Hdst2).

  unfold match_stack in *.
  destruct STK as ((INIT_STK1 & INIT_STK2) & STK).

  destruct set_mem eqn: Hdst_callee.
  { 
    apply set_mem_correct1 in Hdst_callee.

    simpl.
    rewrite decode_str_i_13.
    simpl.

    rewrite HIR13. simpl; rewrite Ptrofs.add_zero_l.

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

    rewrite decode_sub_i; [| auto].

    simpl.
    unfold anextinstr, aadd; simpl.
    repeat abreg_solver_error_prone.
    rewrite REG_DST2 in *.

    rewrite Hdst1 in HALU.
    simpl in HALU.
    injection HALU as Heq; subst i.
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
        apply set_add_intro2; auto.
      * specialize (HSUB _ Hin).
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
          exists (Int.sub v_dst si).
          split; repeat abreg_solver.
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
          { (**r r <> dst /\ r <> src *)
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
          { (**r r <> dst *)
            assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
              rename Hin into HF.
              intro Hin; apply HF.
              apply set_union_elim in Hin.
              destruct Hin as [Hin | Hin].
              - apply set_union_intro1; apply set_add_intro1; auto.
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
    rewrite ptr_int_mul_4.

    rewrite Hdst2.
    rewrite decode_sub_i; [| auto].
    simpl.
    unfold anextinstr, aadd; simpl. repeat abreg_solver_error_prone.
    rewrite REG_DST2 in *.

    rewrite Hdst1 in HALU.
    simpl in HALU.
    injection HALU as Heq; subst i.
    eexists; eexists.
    split; [f_equal |].
    constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; repeat abreg_solver.
    + intros r Hin.
      apply set_add_elim in Hin.
      destruct Hin as [Hin | Hin].
      * subst r.
        apply set_add_intro2; auto.
      * specialize (HSUB _ Hin).
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
          exists (Int.sub v_dst si).
          split; repeat abreg_solver.
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
          destruct REG1 as (vr1 & Hvr1 & Hvr2).
          exists vr1. split; repeat abreg_solver.
        - split.
          + intro HN.
            assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
              intro HF. apply HN.
              apply set_union_elim in HF.
              destruct HF as [HF | HF].
              - apply set_union_intro1.
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
            apply STK1.
          }
        - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
          { (**r r = dst *)
            subst r.
            exfalso. clear - Hin.
            apply Hin.
            apply set_union_intro2. apply set_add_intro2; auto.
          }
          { (**r r <> dst *)
            assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
              rename Hin into HF.
              intro Hin; apply HF.
              apply set_union_elim in Hin.
              destruct Hin as [Hin | Hin].
              - apply set_union_intro1; apply set_add_intro1; auto.
              - apply set_union_intro2; apply set_add_intro1; auto.
            }
            specialize (STK2 Heq); clear Heq. repeat abreg_solver.
          }
      }
  }
Qed.

Lemma exec_alu32_sub_i_0:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.sub (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = true)
    (Hl1 : l2 ++
      [encode_arm32 (encode_arm32 (int_of_breg dst) si 8 4) (encode_arm32 (int_of_breg dst) SUB_I_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  intros.
  unfold jit_call_save_imm in Hsave.
  injection Hsave as Hl2 Hld2 Hst2.
  unfold jit_call_save_add in Hl2.
  destruct set_mem eqn: Hdst_in in Hl2.
  - (**r dst in ld /\ st *)
    subst l2.
    rewrite app_nil_l in Hl1.
    eapply exec_alu32_sub_i_neq_dst_in_ld_set; eauto.
  - (**r dst not in ld /\ st *)
    eapply exec_alu32_sub_i_neq_dst_not_in_ld_set; eauto.
Qed.


Lemma exec_alu32_sub_r1_neq_dst_in_ld_set:
  forall (dst: breg) si l1 ld_set st_set ld_set2 st_set2
    (rs0 rs1: regset) i jit_blk st_blk m1 ars0 astk0 astkb am
    (HALU : Val.sub (rs0 dst) (Vint si) = Vint i)
    (Hdst_in : set_mem breg_eq dst (set_union breg_eq ld_set st_set) = true)
    (Hhi_0 : decode_arm32 si 0 16 = si)
    (Hld2 : set_add breg_eq dst ld_set = ld_set2)
    (Hst2 : set_add breg_eq dst st_set = st_set2)
    (Hl1 : [mov_int_to_movwt si IR11 MOVW_OP;
      encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4)
        (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 =
       BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
         (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  intros.

  inversion HST; subst.
  unfold match_regs in REG.
  specialize (REG dst) as REG_DST.
  apply set_mem_correct1 in Hdst_in.
  unfold set_In in Hdst_in.
  destruct REG_DST as (REG_DST1 & REG_DST2 & REG_DST3).

  specialize (REG_DST1 Hdst_in).
  destruct REG_DST1 as (v_dst & Hdst1 & Hdst2).

  unfold match_stack in *.
  destruct STK as ((INIT_STK1 & INIT_STK2) & STK).

  simpl.
  rewrite decode_movw.
  unfold decode_arm32 in Hhi_0.
  simpl in Hhi_0; rewrite Hhi_0.
  simpl.
  rewrite decode_sub_r; auto.
  simpl.

  unfold anextinstr. repeat abreg_solver_error_prone.
  rewrite Hdst2 in *.
  simpl.
  rewrite Hdst1 in HALU.
  simpl in HALU.
  injection HALU as Heq; subst i.
  eexists; eexists.
  split; [f_equal |].
  constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; repeat abreg_solver.
  + intros r Hin.
    apply set_add_elim in Hin.
    destruct Hin as [Hin | Hin].
    * subst r.
      apply set_add_intro2; auto.
    * specialize (HSUB _ Hin).
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
        exists (Int.sub v_dst si).
        split; repeat abreg_solver.
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
          assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
            intro HF. apply HN.
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
          auto.
        + apply set_union_intro1; auto.
      - apply set_add_elim in H0.
        destruct H0 as [H0 | H0].
        + subst r.
          auto.
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
          apply set_add_intro1; auto.
        + apply set_union_intro2.
          apply set_add_intro1; auto.
    }
Qed.

Lemma exec_alu32_sub_r1_neq_dst_not_in_ld_set:
  forall (dst: breg) si l1 l2 ld_set st_set ld_set2 st_set2
    (rs0 rs1: regset) i jit_blk st_blk m1 ars0 astk0 astkb am
    (HALU : Val.sub (rs0 dst) (Vint si) = Vint i)
    (Hdst_in : set_mem breg_eq dst (set_union breg_eq ld_set st_set) = false)
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = false)
    (Hhi_0 : (decode_arm32 si 0 16) = si)
    (Hld2 : set_add breg_eq dst ld_set = ld_set2)
    (Hst2 : set_add breg_eq dst st_set = st_set2)
    (Hl2 : (if set_mem ireg_eq (ireg_of_breg dst) arm_callee_save
       then
        [jit_alu32_thumb_mem_template_jit STR_I_OP (int_of_breg dst) 
           (int_of_ireg IR13) (Int.mul (int_of_breg dst) (Int.repr 4));
        jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg dst) (int_of_ireg IR12)
          (Int.mul (int_of_breg dst) (Int.repr 4))]
       else
        [jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg dst) 
           (int_of_ireg IR12) (Int.mul (int_of_breg dst) (Int.repr 4))]) = l2)
    (Hl1 : l2 ++
      [mov_int_to_movwt si IR11 MOVW_OP;
      encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4)
        (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16] =
      l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 =
       BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
         (BPregmap.set dst (Vint i) rs0)),
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

  specialize (REG_DST2 Hdst_in).

  assert (Heq: ~ In dst st_set). {
    intro HF; apply Hdst_in.
    apply set_union_intro2; auto.
  }
  specialize (REG_DST3 Heq); clear Heq.
  destruct REG_DST3 as (v_dst & Hdst1 & Hdst2).

  unfold match_stack in *.
  destruct STK as ((INIT_STK1 & INIT_STK2) & STK).

  destruct set_mem eqn: Hdst_callee.
  { 
    apply set_mem_correct1 in Hdst_callee.

    simpl.
    rewrite decode_str_i_13.
    simpl.

    rewrite HIR13. simpl; rewrite Ptrofs.add_zero_l.

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

    rewrite decode_movw.
    unfold decode_arm32 in Hhi_0.
    simpl in Hhi_0; rewrite Hhi_0.
    simpl.

    rewrite decode_sub_r.
    simpl.
    unfold anextinstr, aadd; simpl.
    repeat abreg_solver_error_prone.
    rewrite REG_DST2 in *.

    rewrite Hdst1 in HALU.
    simpl in HALU.
    injection HALU as Heq; subst i.
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
        apply set_add_intro2; auto.
      * specialize (HSUB _ Hin).
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
          exists (Int.sub v_dst si).
          split; repeat abreg_solver.
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
          { (**r r <> dst /\ r <> src *)
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
          { (**r r <> dst *)
            assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
              rename Hin into HF.
              intro Hin; apply HF.
              apply set_union_elim in Hin.
              destruct Hin as [Hin | Hin].
              - apply set_union_intro1; apply set_add_intro1; auto.
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
    rewrite ptr_int_mul_4.

    rewrite Hdst2.
    rewrite decode_movw.
    unfold decode_arm32 in Hhi_0.
    simpl in Hhi_0; rewrite Hhi_0.
    simpl.
    rewrite decode_sub_r.
    simpl.
    unfold anextinstr, aadd; simpl. repeat abreg_solver_error_prone.
    rewrite REG_DST2 in *.

    rewrite Hdst1 in HALU.
    simpl in HALU.
    injection HALU as Heq; subst i.
    eexists; eexists.
    split; [f_equal |].
    constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; repeat abreg_solver.
    + intros r Hin.
      apply set_add_elim in Hin.
      destruct Hin as [Hin | Hin].
      * subst r.
        apply set_add_intro2; auto.
      * specialize (HSUB _ Hin).
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
          exists (Int.sub v_dst si).
          split; repeat abreg_solver.
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
          destruct REG1 as (vr1 & Hvr1 & Hvr2).
          exists vr1. split; repeat abreg_solver.
        - split.
          + intro HN.
            assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
              intro HF. apply HN.
              apply set_union_elim in HF.
              destruct HF as [HF | HF].
              - apply set_union_intro1.
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
            apply STK1.
          }
        - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
          { (**r r = dst *)
            subst r.
            exfalso. clear - Hin.
            apply Hin.
            apply set_union_intro2. apply set_add_intro2; auto.
          }
          { (**r r <> dst *)
            assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
              rename Hin into HF.
              intro Hin; apply HF.
              apply set_union_elim in Hin.
              destruct Hin as [Hin | Hin].
              - apply set_union_intro1; apply set_add_intro1; auto.
              - apply set_union_intro2; apply set_add_intro1; auto.
            }
            specialize (STK2 Heq); clear Heq. repeat abreg_solver.
          }
      }
  }
Qed.

Lemma exec_alu32_sub_r1:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.sub (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = false)
    (Hhi_0 : Int.eq (decode_arm32 si 0 16) si = true)
    (Hl1 : l2 ++
      [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4)
        (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  intros.
  unfold jit_call_save_imm in Hsave.
  injection Hsave as Hl2 Hld2 Hst2.
  unfold jit_call_save_add in Hl2.
  apply Int.same_if_eq in Hhi_0.
  rewrite Hhi_0 in *.
  destruct set_mem eqn: Hdst_in in Hl2.
  - (**r dst in ld /\ st *)
    subst l2.
    rewrite app_nil_l in Hl1.
    eapply exec_alu32_sub_r1_neq_dst_in_ld_set; eauto.
  - (**r dst not in ld /\ st *)
    eapply exec_alu32_sub_r1_neq_dst_not_in_ld_set; eauto.
Qed.

Lemma exec_alu32_sub_r2_neq_dst_in_ld_set:
  forall (dst: breg) si l1 ld_set st_set ld_set2 st_set2
    (rs0 rs1: regset) i jit_blk st_blk m1 ars0 astk0 astkb am
    (HALU : Val.sub (rs0 dst) (Vint si) = Vint i)
    (Hdst_in : set_mem breg_eq dst (set_union breg_eq ld_set st_set) = true)
    (Hld2 : set_add breg_eq dst ld_set = ld_set2)
    (Hst2 : set_add breg_eq dst st_set = st_set2)
    (Hl1 : [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      mov_int_to_movwt (decode_arm32 si 16 16) IR11 MOVT_OP;
      encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4)
        (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 =
       BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
         (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  intros.

  inversion HST; subst.
  unfold match_regs in REG.
  specialize (REG dst) as REG_DST.
  apply set_mem_correct1 in Hdst_in.
  unfold set_In in Hdst_in.
  destruct REG_DST as (REG_DST1 & REG_DST2 & REG_DST3).

  specialize (REG_DST1 Hdst_in).
  destruct REG_DST1 as (v_dst & Hdst1 & Hdst2).

  unfold match_stack in *.
  destruct STK as ((INIT_STK1 & INIT_STK2) & STK).

  simpl.
  rewrite decode_movw.
  assert (Heq: (Int.unsigned_bitfield_extract 0 16 (decode_arm32 si 0 16)) =
    decode_arm32 si 0 16). {
    unfold decode_arm32. simpl.
    apply unsigned_bitfield_extract_same;
    replace Int.zwordsize with 32%Z by reflexivity; try lia.
  }
  rewrite Heq; clear Heq.
  simpl.
  rewrite decode_movt.
  simpl.

  rewrite decode_arm32_0_16_16_equal.

  rewrite decode_sub_r; auto.
  simpl.

  unfold anextinstr. repeat abreg_solver_error_prone.
  rewrite Hdst2 in *.
  simpl.
  rewrite Hdst1 in HALU.
  simpl in HALU.
  injection HALU as Heq; subst i.
  eexists; eexists.
  split; [f_equal |].
  constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; repeat abreg_solver.
  + intros r Hin.
    apply set_add_elim in Hin.
    destruct Hin as [Hin | Hin].
    * subst r.
      apply set_add_intro2; auto.
    * specialize (HSUB _ Hin).
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
        exists (Int.sub v_dst si).
        split; repeat abreg_solver.
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
          assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
            intro HF. apply HN.
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
          auto.
        + apply set_union_intro1; auto.
      - apply set_add_elim in H0.
        destruct H0 as [H0 | H0].
        + subst r.
          auto.
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
          apply set_add_intro1; auto.
        + apply set_union_intro2.
          apply set_add_intro1; auto.
    }
Qed.

Lemma exec_alu32_sub_r2_neq_dst_not_in_ld_set:
  forall (dst: breg) si l1 l2 ld_set st_set ld_set2 st_set2
    (rs0 rs1: regset) i jit_blk st_blk m1 ars0 astk0 astkb am
    (HALU : Val.sub (rs0 dst) (Vint si) = Vint i)
    (Hdst_in : set_mem breg_eq dst (set_union breg_eq ld_set st_set) = false)
    (Hld2 : set_add breg_eq dst ld_set = ld_set2)
    (Hst2 : set_add breg_eq dst st_set = st_set2)
    (Hl2 : (if set_mem ireg_eq (ireg_of_breg dst) arm_callee_save
       then
        [jit_alu32_thumb_mem_template_jit STR_I_OP (int_of_breg dst) 
           (int_of_ireg IR13) (Int.mul (int_of_breg dst) (Int.repr 4));
        jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg dst) (int_of_ireg IR12)
          (Int.mul (int_of_breg dst) (Int.repr 4))]
       else
        [jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg dst) 
           (int_of_ireg IR12) (Int.mul (int_of_breg dst) (Int.repr 4))]) = l2)
    (Hl1 : l2 ++
      [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      mov_int_to_movwt (decode_arm32 si 16 16) IR11 MOVT_OP;
      encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4)
        (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16] =
      l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 =
       BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
         (BPregmap.set dst (Vint i) rs0)),
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

  specialize (REG_DST2 Hdst_in).

  assert (Heq: ~ In dst st_set). {
    intro HF; apply Hdst_in.
    apply set_union_intro2; auto.
  }
  specialize (REG_DST3 Heq); clear Heq.
  destruct REG_DST3 as (v_dst & Hdst1 & Hdst2).

  unfold match_stack in *.
  destruct STK as ((INIT_STK1 & INIT_STK2) & STK).

  destruct set_mem eqn: Hdst_callee.
  { 
    apply set_mem_correct1 in Hdst_callee.

    simpl.
    rewrite decode_str_i_13.
    simpl.

    rewrite HIR13. simpl; rewrite Ptrofs.add_zero_l.

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

    rewrite decode_movw.
    assert (Heq: (Int.unsigned_bitfield_extract 0 16 (decode_arm32 si 0 16)) =
      decode_arm32 si 0 16). {
      unfold decode_arm32. simpl.
      apply unsigned_bitfield_extract_same;
      replace Int.zwordsize with 32%Z by reflexivity; try lia.
    }
    rewrite Heq; clear Heq.
    simpl.
    rewrite decode_movt.
    simpl.

    rewrite decode_arm32_0_16_16_equal.

    rewrite decode_sub_r; auto.
    simpl.

    unfold anextinstr, aadd; simpl.
    repeat abreg_solver_error_prone.
    rewrite REG_DST2 in *.

    rewrite Hdst1 in HALU.
    simpl in HALU.
    injection HALU as Heq; subst i.
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
        apply set_add_intro2; auto.
      * specialize (HSUB _ Hin).
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
          exists (Int.sub v_dst si).
          split; repeat abreg_solver.
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
          { (**r r <> dst /\ r <> src *)
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
          { (**r r <> dst *)
            assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
              rename Hin into HF.
              intro Hin; apply HF.
              apply set_union_elim in Hin.
              destruct Hin as [Hin | Hin].
              - apply set_union_intro1; apply set_add_intro1; auto.
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
    rewrite ptr_int_mul_4.

    rewrite Hdst2.

    rewrite decode_movw.
    assert (Heq: (Int.unsigned_bitfield_extract 0 16 (decode_arm32 si 0 16)) =
      decode_arm32 si 0 16). {
      unfold decode_arm32. simpl.
      apply unsigned_bitfield_extract_same;
      replace Int.zwordsize with 32%Z by reflexivity; try lia.
    }
    rewrite Heq; clear Heq.
    simpl.
    rewrite decode_movt.
    simpl.

    rewrite decode_arm32_0_16_16_equal.

    rewrite decode_sub_r; auto.
    simpl.

    unfold anextinstr, aadd; simpl. repeat abreg_solver_error_prone.
    rewrite REG_DST2 in *.

    rewrite Hdst1 in HALU.
    simpl in HALU.
    injection HALU as Heq; subst i.
    eexists; eexists.
    split; [f_equal |].
    constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; repeat abreg_solver.
    + intros r Hin.
      apply set_add_elim in Hin.
      destruct Hin as [Hin | Hin].
      * subst r.
        apply set_add_intro2; auto.
      * specialize (HSUB _ Hin).
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
          exists (Int.sub v_dst si).
          split; repeat abreg_solver.
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
          destruct REG1 as (vr1 & Hvr1 & Hvr2).
          exists vr1. split; repeat abreg_solver.
        - split.
          + intro HN.
            assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
              intro HF. apply HN.
              apply set_union_elim in HF.
              destruct HF as [HF | HF].
              - apply set_union_intro1.
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
            apply STK1.
          }
        - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
          { (**r r = dst *)
            subst r.
            exfalso. clear - Hin.
            apply Hin.
            apply set_union_intro2. apply set_add_intro2; auto.
          }
          { (**r r <> dst *)
            assert (Heq: ~ In r (set_union breg_eq ld_set st_set)). {
              rename Hin into HF.
              intro Hin; apply HF.
              apply set_union_elim in Hin.
              destruct Hin as [Hin | Hin].
              - apply set_union_intro1; apply set_add_intro1; auto.
              - apply set_union_intro2; apply set_add_intro1; auto.
            }
            specialize (STK2 Heq); clear Heq. repeat abreg_solver.
          }
      }
  }
Qed.

Lemma exec_alu32_sub_r2:
  forall (rs0 rs1: regset) (dst: breg) si i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.sub (rs0 dst) (Vint si) = Vint i)
    (Hsave : jit_call_save_imm dst ld_set st_set = (l2, ld_set2, st_set2))
    (Hle_255 : Int.cmpu Cle Int.zero si && Int.cmpu Cle si (Int.repr 255) = false)
    (Hl1 : l2 ++
      [mov_int_to_movwt (decode_arm32 si 0 16) IR11 MOVW_OP;
      mov_int_to_movwt (decode_arm32 si 16 16) IR11 MOVT_OP;
      encode_arm32 (encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4)
        (encode_arm32 (int_of_breg dst) SUB_R_OP 0 4) 16 16] = l1)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1) (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 = BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone) (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1) (AState ars1 astk1 astkb am).
Proof.
  intros.
  unfold jit_call_save_imm in Hsave.
  injection Hsave as Hl2 Hld2 Hst2.
  unfold jit_call_save_add in Hl2.
  destruct set_mem eqn: Hdst_in in Hl2.
  - (**r dst in ld /\ st *)
    subst l2.
    rewrite app_nil_l in Hl1.
    eapply exec_alu32_sub_r2_neq_dst_in_ld_set; eauto.
  - (**r dst not in ld /\ st *)
    eapply exec_alu32_sub_r2_neq_dst_not_in_ld_set; eauto.
Qed.