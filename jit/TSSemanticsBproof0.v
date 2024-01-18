From compcert.lib Require Import Integers Coqlib Maps.
From compcert.common Require Import AST Values Memory.
From compcert.arm Require Import AsmSyntax ABinSem BinDecode BinSyntax  Conventions1 Machregs.

From bpf.comm Require Import JITCall.
From bpf.rbpf32 Require Import TSSyntax JITConfig.
From bpf.jit Require Import Arm32Reg ThumbInsOp ThumbJIT WholeCompiler.
From bpf.jit Require Import ThumbJITLtac ABMemory TSSemanticsB ThumbJITProofLemma0 TSSemanticsBproofdef.
From bpf.jit Require Import ThumbDecodeEncodeALU ThumbDecodeEncodeMEM.
From Coq Require Import ZArith Lia List ListSet.

Open Scope nat_scope.
Open Scope asm.
Import ListNotations.

Lemma exec_alu32_add_r_eq_dst_in_ld_set:
  forall l2 dst l1 ld_set st_set ld_set2 st_set2 (rs0 rs1: regset) i jit_blk st_blk m1 ars0 astk0 astkb am
    (Hl1 : l2 ++
      [encode_arm32
         (encode_arm32
            (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
            (encode_arm32 (int_of_ireg (ireg_of_breg dst))
               (encode_arm32
                  (if Int.lt (int_of_breg dst) (Int.repr 8)
                   then int_of_breg dst
                   else Int.sub (int_of_breg dst) (Int.repr 8)) ADD_R_OP 0 3) 3 4) 7 1)
         NOP_OP 16 16] = l1)
    (Hdst_in : set_mem breg_eq dst ld_set = true)
    (Hl2 :
      (if set_mem breg_eq dst (set_add breg_eq dst ld_set)
       then []
       else
        if set_mem breg_eq dst rbpf_arm_callee_save
        then
         [jit_alu32_thumb_mem_template_jit STR_I_OP (int_of_breg dst)
            (int_of_ireg IR13) (Int.mul (int_of_breg dst) (Int.repr 4));
         jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg dst) 
           (int_of_ireg IR12) (Int.mul (int_of_breg dst) (Int.repr 4))]
        else
         [jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg dst)
            (int_of_ireg IR12) (Int.mul (int_of_breg dst) (Int.repr 4))]) = l2)
    (Hld2 : set_add breg_eq dst (set_add breg_eq dst ld_set) = ld_set2)
    (Hst2 : set_add breg_eq dst st_set = st_set2)
    (HALU : Val.add (rs0 dst) (rs0 dst) = Vint i)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1)
            (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 =
           BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
             (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1)
          (AState ars1 astk1 astkb am).
Proof.
  intros.
  assert (Heq: set_mem breg_eq dst (set_add breg_eq dst ld_set) = true). {
    apply set_mem_correct2. listset_solver.
  }
  rewrite Heq in Hl2; clear Heq.
  simpl in Hl2.
  subst l2.
  subst l1.
  simpl.


  assert (Heq: is_final_state ars0 = false). {
    unfold is_final_state.
    inversion HST; subst.
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

  rewrite decode_add_r.
  simpl.

  inversion HST; subst.
  unfold match_regs in REG.
  specialize (REG dst) as REG_DST.
  apply set_mem_correct1 in Hdst_in.
  unfold set_In in Hdst_in.
  destruct REG_DST as (REG_DST & _).

  assert (Hdst_in_union: In dst (set_union breg_eq ld_set st_set)) by listset_solver.
  specialize (REG_DST Hdst_in_union).
  destruct REG_DST as (v_dst & Hdst_1 & Hdst_2).
  rewrite Hdst_2 in *.
  simpl.


  assert (Heq: is_final_state (anextinstr_nf true
         ars0 # (ireg_of_breg dst) <- (Cval (Vint (Int.add v_dst v_dst)))) = false). {
    unfold is_final_state.
    assert (Heq: aval_eq (anextinstr_nf true
     ars0 # (ireg_of_breg dst) <- (Cval (Vint (Int.add v_dst v_dst))) IR13)
      (Aval (Rval (Sreg IR13))) = false).
    - unfold anextinstr_nf, anextinstr, aundef_flags.
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

  rewrite Hdst_1 in HALU.
  simpl in HALU.
  injection HALU as Heq; subst i.
  eexists; eexists.
  split; [f_equal |].
  constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; repeat abreg_solver.
  - intros.
    specialize (Hfloat _ H).
      repeat float_preg_of_solver.
      repeat (destruct H as [H | H];
          [subst x; auto|]); inversion H.

  - destruct HNoDup as (HNoDup1 & HNoDup2);
    split; repeat apply set_add_nodup; auto.

  - repeat abreg_solver_error_prone.
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

  - destruct HIRPC as (va_pc & HIRPC).
    unfold aoffset_ptr.
    repeat abreg_solver_error_prone.
    rewrite Pregmap.gso. 2:{ unfold ireg_of_breg; intro HF; inversion HF. }
    rewrite HIRPC.
    simpl.
    eexists; f_equal.

  - intros r Hin.
    repeat listset_context_solver.
  - unfold match_regs.
    intros.
    specialize (REG r).
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
        exists (Int.add v_dst v_dst).
        split; repeat abreg_solver.
      - split.
        + intro Hnot_in.
          exfalso.
          apply Hnot_in.
          listset_solver.
        + intros Hnot_in.
          exfalso.
          apply Hnot_in.
          listset_solver.
    }
    { (**r r <> dst *)
      split.
      - intros.
        assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
        specialize (REG1 Heq); clear Heq.
        destruct REG1 as (vr & Hvr1 & Hvr2).
        exists vr.
        split; repeat abreg_solver.
      - split.
        + intro HN. destruct HN as (HN & HN1).
          assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
            In r rbpf_arm_callee_save). {
            split; auto.
            listset_solver.
          }
          specialize (REG2 Heq); clear Heq.
          repeat abreg_solver.
        + intro HN.
          assert (Heq: ~ In r st_set) by listset_solver.
          specialize (REG3 Heq); clear Heq.
          destruct REG3 as (vr & Hvr1 & Hvr2).
          exists vr.
          split; repeat abreg_solver.
    }

  - unfold match_stack in *.
    destruct STK as (INIT_STK & STK).
    split; [auto | ].
    intros.
    specialize (STK r H).
    destruct STK as (STK1 & STK2).
    split; intros.
    {
      apply STK1. listset_solver.
    }
    {
      destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
      - (**r r = dst *)
        subst r.
        exfalso.
        apply H0.
        clear. listset_solver.
      - (**r r <> dst *)
        repeat abreg_solver.
        apply STK2.
        split; auto.
        intro HF.
        apply H0. listset_solver.
    }
Qed.

Lemma exec_alu32_add_r_eq_dst_not_in_ld_set:
  forall l2 dst l1 ld_set st_set ld_set2 st_set2 (rs0 rs1: regset) i jit_blk st_blk m1 ars0 astk0 astkb am
    (Hl1 : l2 ++
      [encode_arm32
         (encode_arm32
            (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
            (encode_arm32 (int_of_ireg (ireg_of_breg dst))
               (encode_arm32
                  (if Int.lt (int_of_breg dst) (Int.repr 8)
                   then int_of_breg dst
                   else Int.sub (int_of_breg dst) (Int.repr 8)) ADD_R_OP 0 3) 3 4) 7 1)
         NOP_OP 16 16] = l1)
    (Hdst_in : set_mem breg_eq dst ld_set = false)
    (Hl2 : (if set_mem breg_eq dst rbpf_arm_callee_save
       then
        [jit_alu32_thumb_mem_template_jit STR_I_OP (int_of_breg dst) 
           (int_of_ireg IR13) (Int.mul (int_of_breg dst) (Int.repr 4));
        jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg dst) 
          (int_of_ireg IR12) (Int.mul (int_of_breg dst) (Int.repr 4))]
       else
        [jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg dst) 
           (int_of_ireg IR12) (Int.mul (int_of_breg dst) (Int.repr 4))]) ++
      (if set_mem breg_eq dst (set_add breg_eq dst ld_set)
       then []
       else
        if set_mem breg_eq dst rbpf_arm_callee_save
        then
         [jit_alu32_thumb_mem_template_jit STR_I_OP (int_of_breg dst)
            (int_of_ireg IR13) (Int.mul (int_of_breg dst) (Int.repr 4));
         jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg dst) 
           (int_of_ireg IR12) (Int.mul (int_of_breg dst) (Int.repr 4))]
        else
         [jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg dst)
            (int_of_ireg IR12) (Int.mul (int_of_breg dst) (Int.repr 4))]) = l2)
    (Hld2 : set_add breg_eq dst (set_add breg_eq dst ld_set) = ld_set2)
    (Hst2 : set_add breg_eq dst st_set = st_set2)
    (HALU : Val.add (rs0 dst) (rs0 dst) = Vint i)
    (HST : match_states jit_blk st_blk ld_set st_set (State rs0 m1)
        (AState ars0 astk0 astkb am))
    (Hrs1 : rs1 =
       BPregmap.set BPC (Val.add (BPregmap.set dst (Vint i) rs0 BPC) Vone)
         (BPregmap.set dst (Vint i) rs0)),
      exists (ars1 : aregset) (astk1 : astack),
        exec_bin_list l1 ars0 astk0 astkb am = ANext ars1 astk1 astkb am /\
        match_states jit_blk st_blk ld_set2 st_set2 (State rs1 m1)
          (AState ars1 astk1 astkb am).
Proof.
  intros.
  apply set_mem_complete1 in Hdst_in.

  assert (Heq: set_mem breg_eq dst (set_add breg_eq dst ld_set) = true). {
    apply set_mem_correct2.
    apply set_add_intro2; auto.
  }
  rewrite Heq in Hl2; clear Heq.
  rewrite app_nil_r in Hl2.
  unfold jit_alu32_thumb_mem_template_jit in Hl2.

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

  destruct set_mem eqn: Hdst_callee.
  -
    assert (Heq: ~ In dst (set_union breg_eq ld_set st_set) /\
    In dst rbpf_arm_callee_save). {
      apply set_mem_correct1 in Hdst_callee.
      split; auto.
      intro HF; apply Hdst_in. listset_solver.
    }
    specialize (REG2 Heq); clear Heq.

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

    rewrite set_add_same.

    rewrite decode_ldr_i_12.
    remember (setN (encode_sval_fragments Cany32 (Rval (Sreg (ireg_of_breg dst))))
     (z_of_breg dst * 4) astk0) as astk1 eqn: Hastk1_eq.
    simpl.
    unfold anextinstr at 1. abreg_solver_error_prone.
    rewrite HIR12.
    simpl. rewrite Ptrofs.add_zero_l.

    rewrite ptr_int_mul_4.

    rewrite Hdst2.

    assert (Heq: is_final_state (anextinstr true
         (anextinstr true ars0) # (ireg_of_breg dst) <- (Cval (Vint v_dst))) = false). {
      unfold is_final_state.
      assert (Heq: aval_eq (anextinstr true
     (anextinstr true ars0) # (ireg_of_breg dst) <- (Cval (Vint v_dst)) IR13)
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

    rewrite decode_add_r.
    unfold anextinstr; simpl. repeat abreg_solver_error_prone.

    simpl.

    assert (Heq: is_final_state (anextinstr_nf true
         (((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize))
           # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
          (aoffset_ptr
             ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize))
              # (ireg_of_breg dst) <- (Cval (Vint v_dst)) PC) wsize))
         # (ireg_of_breg dst) <- (Cval (Vint (Int.add v_dst v_dst)))) = false). {
      unfold is_final_state.
      assert (Heq: aval_eq (anextinstr_nf true
     (((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize)) # 
       (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
      (aoffset_ptr
         ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize)) # 
          (ireg_of_breg dst) <- (Cval (Vint v_dst)) PC) wsize))
     # (ireg_of_breg dst) <- (Cval (Vint (Int.add v_dst v_dst))) IR13)
        (Aval (Rval (Sreg IR13))) = false).
      - unfold anextinstr_nf, anextinstr, aundef_flags.
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

    eexists. exists astk1.
    split; [f_equal |].

    constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; simpl; repeat abreg_solver.
    + intros.
      specialize (Hfloat _ H).
      repeat float_preg_of_solver.
      repeat (destruct H as [H | H];
          [subst x; auto|]); inversion H.
    + destruct HNoDup as (HNoDup1 & HNoDup2);
      split; repeat apply set_add_nodup; auto.

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
        repeat abreg_solver_error_prone.
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
      rewrite Pregmap.gso. 2:{ unfold ireg_of_breg; intro HF; inversion HF. }
      rewrite HIRPC.
      rewrite Pregmap.gss.
      simpl.
      eexists; f_equal.

    + intros r Hin. listset_solver.

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
          assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
          specialize (REG1 Heq); clear Heq.
          destruct REG1 as (vr_r & Hvr_r1 & Hvr_r2).
          exists vr_r.
          split; repeat abreg_solver.
        }
      * split; intro HF. destruct HF as (HF & HF1).
        { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
          { (**r r = dst *)
            subst r.
            exfalso; apply HF; clear. listset_solver.
          }
          { (**r r <> dst *)
            assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
              In r rbpf_arm_callee_save). {
              split; auto.
              intro Hin; apply HF. listset_solver.
            }
            specialize (REG2 Heq); clear Heq.

            rename HF into Hno_in.
            repeat abreg_solver.
          }
        }
        { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
          { (**r r = dst *)
            subst r.
            exfalso; apply HF; clear. listset_solver.
          }
          { (**r r <> dst *)
            assert (Heq: ~ In r st_set). {
              intro Hin; apply HF. listset_solver.
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
            assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
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
            apply Hin. listset_solver.
          }
          { (**r r <> dst *) destruct Hin as (Hin & Hin1).
            assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
              In r rbpf_arm_callee_save). {
              split; auto.
              rename Hin into HF.
              intro Hin; apply HF. listset_solver.
            }
            specialize (STK2 Heq); clear Heq.
            repeat abreg_solver.
          }
      }
  - simpl.

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

    assert (Heq: is_final_state (anextinstr true ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) = false). {
      unfold is_final_state.
      assert (Heq: aval_eq ((anextinstr true ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) IR13) (Aval (Rval (Sreg IR13))) = false).
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

    rewrite decode_add_r.
    rewrite set_add_same.

    unfold anextinstr; simpl. repeat abreg_solver_error_prone.
    simpl.

    assert (Heq: is_final_state (anextinstr_nf true
         ((ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
          (aoffset_ptr (ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst)) PC)
             wsize)) # (ireg_of_breg dst) <-
         (Cval (Vint (Int.add v_dst v_dst)))) = false). {
      unfold is_final_state.
      assert (Heq: aval_eq ((anextinstr_nf true
         ((ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
          (aoffset_ptr (ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst)) PC)
             wsize)) # (ireg_of_breg dst) <-
         (Cval (Vint (Int.add v_dst v_dst)))) IR13) (Aval (Rval (Sreg IR13))) = false).
      - unfold anextinstr_nf, anextinstr, aundef_flags.
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


    eexists. exists astk0.
    split; [f_equal |].

    constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; simpl; repeat abreg_solver.
    + intros.
      specialize (Hfloat _ H).
      repeat float_preg_of_solver.
      repeat (destruct H as [H | H];
          [subst x; auto|]); inversion H.
    + destruct HNoDup as (HNoDup1 & HNoDup2);
      split; repeat apply set_add_nodup; auto.

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
        repeat abreg_solver_error_prone.
        rewrite Pregmap.gso.
        2:{ intro HF. apply Hr_neq. injection HF as Heq. assumption. }
        repeat abreg_solver.
      }

    + destruct HIRPC as (va_pc & HIRPC).
      unfold aoffset_ptr.
      repeat abreg_solver_error_prone.
      rewrite Pregmap.gso. 2:{ unfold ireg_of_breg; intro HF; inversion HF. }
      rewrite Pregmap.gss.
      rewrite Pregmap.gso. 2:{ unfold ireg_of_breg; intro HF; inversion HF. }
      rewrite HIRPC.
      simpl.
      eexists; f_equal.

    + intros r Hin.
      apply set_add_elim in Hin.
      destruct Hin as [Hin | Hin].
      * subst r. listset_solver.
      * listset_solver.

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
          assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
          specialize (REG1 Heq); clear Heq.
          destruct REG1 as (vr_r & Hvr_r1 & Hvr_r2).
          exists vr_r.
          split; repeat abreg_solver.
        }
      * split; intro HF. destruct HF as (HF & HF1).
        { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
          { (**r r = dst *)
            subst r.
            exfalso; apply HF; clear. listset_solver.
          }
          { (**r r <> dst *)
            assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
                In r rbpf_arm_callee_save). {
              split; auto.
              intro Hin; apply HF. listset_solver.
            }
            specialize (REG2 Heq); clear Heq.

            rename HF into Hno_in.
            repeat abreg_solver.
          }
        }
        { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
          { (**r r = dst *)
            subst r.
            exfalso; apply HF; clear. listset_solver.
          }
          { (**r r <> dst *)
            assert (Heq: ~ In r st_set). {
              intro Hin; apply HF. listset_solver.
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
            apply STK1. listset_solver.
          }
        - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
          { (**r r = dst *)
            subst r.
            exfalso. clear - Hin.
            apply Hin. listset_solver.
          }
          { (**r r <> dst *) destruct Hin as (Hin & Hin1).
            assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
              In r rbpf_arm_callee_save). {
              split; auto. listset_solver.
            }
            specialize (STK2 Heq); clear Heq.
            repeat abreg_solver.
          }
      }
Qed.

Lemma exec_alu32_add_r_neq_dst_in_ld_set:
  forall l2 (dst src: breg) l1 ld_set st_set ld_set2 st_set2
    (rs0 rs1: regset) i jit_blk st_blk m1 ars0 astk0 astkb am
    (HALU : Val.add (rs0 dst) (rs0 src) = Vint i)
    (Hdst_in : set_mem breg_eq dst ld_set = true)
    (Hl2 :
      (if set_mem breg_eq src (set_add breg_eq dst ld_set)
       then []
       else
        if set_mem breg_eq src rbpf_arm_callee_save
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
                   else Int.sub (int_of_breg dst) (Int.repr 8)) ADD_R_OP 0 3) 3 4) 7 1) NOP_OP 16
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

  assert (Hdst_in_union: In dst (set_union breg_eq ld_set st_set)) by listset_solver.
  specialize (REG_DST1 Hdst_in_union).
  destruct REG_DST1 as (v_dst & Hdst1 & Hdst2).

  unfold jit_alu32_thumb_mem_template_jit.

  unfold match_stack in *.
  destruct STK as ((INIT_STK1 & INIT_STK2) & STK).

  destruct set_mem eqn: Hsrc_in.
  - (**r src in ld_set *)
    rewrite app_nil_l.
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

    rewrite decode_add_r.
    simpl.

    apply set_mem_correct1 in Hsrc_in.
    apply set_add_elim in Hsrc_in.
    destruct Hsrc_in as [Hsrc_in | Hsrc_in]; [exfalso; apply Hreg_neq; auto |].
    assert (Hsrc_in_union: In src (set_union breg_eq ld_set st_set)) by listset_solver.

    specialize (REG_SRC1 Hsrc_in_union).
    destruct REG_SRC1 as (v_src & Hsrc1 & Hsrc2).
    rewrite Hdst2, Hsrc2 in *.
    simpl.

    assert (Heq: is_final_state (anextinstr_nf true
         ars0 # (ireg_of_breg dst) <- (Cval (Vint (Int.add v_dst v_src)))) = false). {
      unfold is_final_state.
      assert (Heq: aval_eq ((anextinstr_nf true
         ars0 # (ireg_of_breg dst) <- (Cval (Vint (Int.add v_dst v_src)))) IR13)
        (Aval (Rval (Sreg IR13))) = false).
      - unfold anextinstr_nf, anextinstr, aundef_flags.
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

    rewrite Hdst1, Hsrc1 in HALU.
    simpl in HALU.
    injection HALU as Heq; subst i.
    eexists; eexists.
    split; [f_equal |].
    constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; repeat abreg_solver.
    + intros.
      specialize (Hfloat _ H). repeat float_preg_of_solver.
      repeat (destruct H as [H | H];
          [subst x; auto|]); inversion H.
    + destruct HNoDup as (HNoDup1 & HNoDup2);
      split; repeat apply set_add_nodup; auto.

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

    + intros r Hin. listset_solver.
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
          exists (Int.add v_dst v_src).
          split; repeat abreg_solver.
        - split.
          + intro Hnot_in.
            exfalso.
            apply Hnot_in.  listset_solver.
          + intros Hnot_in.
            exfalso.
            apply Hnot_in.  listset_solver.
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
            apply Hnot_in. listset_solver.
          + intros Hnot_in.
            assert (Heq: ~ In src st_set) by listset_solver.
            specialize (REG3 Heq); clear Heq.
            destruct REG3 as (vr & Hvr3 & Hvr4).
            exists vr.
            split; repeat abreg_solver.
      }
      { (**r r <> dst /\ r <> src *)
        split.
        - intros.
          assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
          specialize (REG1 Heq); clear Heq.
          destruct REG1 as (vr & Hvr1 & Hvr2).
          exists vr.
          split; repeat abreg_solver.
        - split.
          + intro HN. destruct HN as (HN & HN1).
            assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
              In r rbpf_arm_callee_save). {
              split; auto.
              intro HF. apply HN. listset_solver.
            }
            specialize (REG2 Heq); clear Heq.
            repeat abreg_solver.
          + intro HN.
            assert (Heq: ~ In r st_set) by listset_solver.
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
        apply STK1. listset_solver.
      }
      {
        destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
        - (**r r = dst *)
          subst r.
          exfalso.
          apply H0.
          clear. listset_solver.
        - (**r r <> dst *)
          repeat abreg_solver.
          apply STK2.
          split; auto.
          intro HF.
          apply H0. listset_solver.
      }
  - (**r src not in ld_set *)
    apply set_mem_complete1 in Hsrc_in.

    assert (Heq: ~In src ld_set). {
      intro HF; apply Hsrc_in. listset_solver.
    }
    clear Hsrc_in; rename Heq into Hsrc_in.

    assert (Heq: ~ In src st_set) by listset_solver.
    specialize (REG_SRC3 Heq); clear Heq.
    destruct REG_SRC3 as (v_src & Hsrc1 & Hsrc2).

    destruct set_mem eqn: Hcallee.
    {
      assert (Heq: ~ In src (set_union breg_eq ld_set st_set) /\
        In src rbpf_arm_callee_save). {
        apply set_mem_correct1 in Hcallee.
        split; auto. listset_solver.
      }
      specialize (REG_SRC2 Heq); clear Heq.

      apply set_mem_correct1 in Hcallee.
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
      remember (setN (encode_sval_fragments Cany32 (Rval (Sreg (ireg_of_breg _))))
       _ astk0) as astk1 eqn: Hastk1_eq.
      simpl.
      unfold anextinstr at 1. repeat abreg_solver_error_prone.
      rewrite HIR12.
      simpl. rewrite Ptrofs.add_zero_l.

      rewrite ptr_int_mul_4.

      rewrite Hsrc2.
      rewrite decode_add_r.
      unfold anextinstr; simpl. repeat abreg_solver_error_prone.

      assert (Heq: is_final_state (((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize)) # 
         (ireg_of_breg src) <- (Cval (Vint v_src))) # PC <-
        (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize)) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq ((((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize)) # 
         (ireg_of_breg src) <- (Cval (Vint v_src))) # PC <-
        (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize)) IR13)
          (Aval (Rval (Sreg IR13))) = false).
        - repeat abreg_solver_error_prone.
          rewrite HIR13.
          simpl.
          auto.
        - rewrite Heq.
          rewrite andb_false_r.
          rewrite andb_false_l.
          auto.
      }
      rewrite Heq; clear Heq.

      rewrite Hdst2.
      simpl.

      assert (Heq: is_final_state (anextinstr_nf true
         (((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize))
           # (ireg_of_breg src) <- (Cval (Vint v_src))) # PC <-
          (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize))
         # (ireg_of_breg dst) <- (Cval (Vint (Int.add v_dst v_src)))) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq ((anextinstr_nf true
         (((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize))
           # (ireg_of_breg src) <- (Cval (Vint v_src))) # PC <-
          (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize))
         # (ireg_of_breg dst) <- (Cval (Vint (Int.add v_dst v_src)))) IR13)
          (Aval (Rval (Sreg IR13))) = false).
        - unfold anextinstr_nf, anextinstr, aundef_flags.
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

      eexists. exists astk1.
      split; [f_equal |].

      constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; simpl; repeat abreg_solver.
      + intros.
        specialize (Hfloat _ H).
        repeat float_preg_of_solver.
        repeat (destruct H as [H | H];
            [subst x; auto|]); inversion H.
      + destruct HNoDup as (HNoDup1 & HNoDup2);
        split; repeat apply set_add_nodup; auto.

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
        repeat abreg_solver_error_prone.

        destruct (ireg_eq IR0 (ireg_of_breg src)) as [Hrs_eq | Hrs_neq].
        { (**r r = src *)
          rewrite <- Hrs_eq.
          repeat abreg_solver_error_prone.
          simpl.
          reflexivity.
        }
        { (**r r <> src *)
          rewrite Pregmap.gso.
          2:{ intro HF. apply Hrs_neq. injection HF as Heq. assumption. }
          repeat abreg_solver.
        }
      }

      + clear - HAR11 Hastk1_eq.
        unfold astack_load in *.
        destruct Mem.valid_access_dec; [| inversion HAR11].
        subst astk1.
        rewrite ab_getN_setN_outside; [auto | ].
        right. simpl.
        destruct src; simpl; lia.

      + destruct HIRPC as (va_pc & HIRPC).
        unfold aoffset_ptr.
        repeat abreg_solver_error_prone.
        rewrite Pregmap.gso. 2:{ unfold ireg_of_breg; intro HF; inversion HF. }
        rewrite Pregmap.gss.
        rewrite HIRPC.
        simpl.
        eexists; f_equal.

      + intros r Hin.  listset_solver.

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
            rewrite <- HALU. rewrite Hsrc1, Hdst1. simpl; auto.
          }
          destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
          { (**r r = src *)
            subst r.
            exists v_src.
            split; repeat abreg_solver.
          }
          { (**r r <> dst /\ r<> src *)
            assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
            specialize (REG1 Heq); clear Heq.
            destruct REG1 as (vr_r & Hvr_r1 & Hvr_r2).
            exists vr_r.
            split; repeat abreg_solver.
          }
        * split; intro HF. destruct HF as (HF & HF1).
          { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso; apply HF; clear. listset_solver.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso; apply HF; clear. listset_solver.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
                In r rbpf_arm_callee_save). {
                split; auto.
                intro Hin; apply HF. listset_solver.
              }
              specialize (REG2 Heq); clear Heq.

              rename HF into Hno_in.
              repeat abreg_solver.
            }
          }
          { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso; apply HF; clear. listset_solver.
            }
            { (**r r <> dst *)
              assert (Heq: ~ In r st_set). {
                intro Hin; apply HF. listset_solver.
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
              assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
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
              apply Hin. listset_solver.
            }
            { (**r r <> dst /\ r <> src *) destruct Hin as (Hin & Hin1).
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
                In r rbpf_arm_callee_save). {
                split; auto. listset_solver.
              }
              specialize (STK2 Heq); clear Heq.
              repeat abreg_solver.
            }
          }
    }

    { simpl.

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

      rewrite Hsrc2.

      rewrite decode_add_r.
      unfold anextinstr; simpl. repeat abreg_solver_error_prone.

      assert (Heq: is_final_state ((ars0 # (ireg_of_breg src) <- (Cval (Vint v_src))) # PC <-
      (aoffset_ptr (ars0 PC) wsize)) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq (((ars0 # (ireg_of_breg src) <- (Cval (Vint v_src))) # PC <-
      (aoffset_ptr (ars0 PC) wsize)) IR13)
          (Aval (Rval (Sreg IR13))) = false).
        - repeat abreg_solver_error_prone.
          rewrite HIR13.
          simpl.
          auto.
        - rewrite Heq.
          rewrite andb_false_r.
          rewrite andb_false_l.
          auto.
      }
      rewrite Heq; clear Heq.

      rewrite Hdst2.
      simpl.

      assert (Heq: is_final_state (anextinstr_nf true
         ((ars0 # (ireg_of_breg src) <- (Cval (Vint v_src))) # PC <-
          (aoffset_ptr (ars0 PC) wsize)) # (ireg_of_breg dst) <-
         (Cval (Vint (Int.add v_dst v_src)))) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq ((anextinstr_nf true
         ((ars0 # (ireg_of_breg src) <- (Cval (Vint v_src))) # PC <-
          (aoffset_ptr (ars0 PC) wsize)) # (ireg_of_breg dst) <-
         (Cval (Vint (Int.add v_dst v_src)))) IR13)
          (Aval (Rval (Sreg IR13))) = false).
        - unfold anextinstr_nf, anextinstr, aundef_flags.
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

      eexists. exists astk0.
      split; [f_equal |].

      constructor; auto; unfold anextinstr_nf; unfold anextinstr, aundef_flags;
        simpl; repeat abreg_solver.
      + intros.
        specialize (Hfloat _ H).
        repeat float_preg_of_solver.
        repeat (destruct H as [H | H];
            [subst x; auto|]); inversion H.

      + destruct HNoDup as (HNoDup1 & HNoDup2);
        split; repeat apply set_add_nodup; auto.

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
          repeat abreg_solver_error_prone.
          destruct (ireg_eq IR0 (ireg_of_breg src)) as [Hrs_eq | Hrs_neq].
          { (**r r = src *)
            rewrite <- Hrs_eq.
            repeat abreg_solver_error_prone.
            simpl.
            reflexivity.
          }
          { (**r r <> src *)
            rewrite Pregmap.gso.
            2:{ intro HF. apply Hrs_neq. injection HF as Heq. assumption. }
            repeat abreg_solver.
          }
        }

      + destruct HIRPC as (va_pc & HIRPC).
        unfold aoffset_ptr.
        repeat abreg_solver_error_prone.
        rewrite Pregmap.gso. 2:{ unfold ireg_of_breg; intro HF; inversion HF. }
        rewrite Pregmap.gss.
        rewrite HIRPC.
        simpl.
        eexists; f_equal.

      + intros r Hin. listset_solver.

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
            rewrite <- HALU. rewrite Hdst1, Hsrc1. simpl; auto.
          }
          destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
          { (**r r = src *)
            subst r.
            exists v_src.
            split; repeat abreg_solver.
          }
          { (**r r <> dst /\ r<> src *)
            assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
            specialize (REG1 Heq); clear Heq.
            destruct REG1 as (vr_r & Hvr_r1 & Hvr_r2).
            exists vr_r.
            split; repeat abreg_solver.
          }
        * split; intro HF. destruct HF as (HF & HF1).
          { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso; apply HF; clear. listset_solver.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso; apply HF; clear.
              apply set_union_intro1.
              apply set_add_intro2; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
                In r rbpf_arm_callee_save). {
                split; auto. 
                intro Hin; apply HF. listset_solver.
              }
              specialize (REG2 Heq); clear Heq.

              rename HF into Hno_in. repeat abreg_solver.
            }
          }
          { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso; apply HF; clear. listset_solver.
            }
            { (**r r <> dst *)
              assert (Heq: ~ In r st_set). {
                intro Hin; apply HF. listset_solver.
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
              2:{ listset_solver. }
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
              assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
              specialize (STK1 Heq); clear Heq.
              rewrite <- STK1. auto.
            }
          - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso. clear - Hin.
              apply Hin. listset_solver.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso. clear - Hin.
              apply Hin. listset_solver.
            }
            { (**r r <> dst /\ r <> src *) destruct Hin as (Hin & Hin1).
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
                In r rbpf_arm_callee_save). {
                split; auto. listset_solver.
              }
              specialize (STK2 Heq); clear Heq.
              repeat abreg_solver.
            }
          }
    }
Qed.


Lemma exec_alu32_add_r_neq_dst_not_in_ld_set:
  forall l2 (dst src: breg) l1 ld_set st_set ld_set2 st_set2
    (rs0 rs1: regset) i jit_blk st_blk m1 ars0 astk0 astkb am
    (HALU : Val.add (rs0 dst) (rs0 src) = Vint i)
    (Hdst_in : set_mem breg_eq dst ld_set = false)
    (Hl2 : (if set_mem breg_eq dst rbpf_arm_callee_save
       then
        [jit_alu32_thumb_mem_template_jit STR_I_OP (int_of_breg dst) (int_of_ireg IR13)
           (Int.mul (int_of_breg dst) (Int.repr 4));
        jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg dst) (int_of_ireg IR12)
          (Int.mul (int_of_breg dst) (Int.repr 4))]
       else
        [jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg dst) (int_of_ireg IR12)
           (Int.mul (int_of_breg dst) (Int.repr 4))]) ++
      (if set_mem breg_eq src (set_add breg_eq dst ld_set)
       then []
       else
        if set_mem breg_eq src rbpf_arm_callee_save
        then
         [jit_alu32_thumb_mem_template_jit STR_I_OP (int_of_breg src) (int_of_ireg IR13)
            (Int.mul (int_of_breg src) (Int.repr 4));
         jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg src) (int_of_ireg IR12)
           (Int.mul (int_of_breg src) (Int.repr 4))]
        else
         [jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg src) (int_of_ireg IR12)
            (Int.mul (int_of_breg src) (Int.repr 4))]) = l2)
    (Hld2 : set_add breg_eq src (set_add breg_eq dst ld_set) = ld_set2)
    (Hst2 : set_add breg_eq dst st_set = st_set2)
    (Hl1 : l2 ++
      [encode_arm32
         (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
            (encode_arm32 (int_of_ireg (ireg_of_breg src))
               (encode_arm32
                  (if Int.lt (int_of_breg dst) (Int.repr 8)
                   then int_of_breg dst
                   else Int.sub (int_of_breg dst) (Int.repr 8)) ADD_R_OP 0 3) 3 4) 7 1) NOP_OP 16
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

  assert (Heq: ~ In dst st_set) by  listset_solver.
  specialize (REG_DST3 Heq); clear Heq.
  destruct REG_DST3 as (v_dst & Hdst1 & Hdst2).

  unfold match_stack in *.
  destruct STK as ((INIT_STK1 & INIT_STK2) & STK).

  destruct set_mem eqn: Hdst_callee.
  {
    assert (Heq: ~ In dst (set_union breg_eq ld_set st_set) /\
      In dst rbpf_arm_callee_save). {
      apply set_mem_correct1 in Hdst_callee.
      split; auto. listset_solver.
    }
    specialize (REG_DST2 Heq); clear Heq.

    apply set_mem_correct1 in Hdst_callee.
    destruct set_mem eqn: Hsrc_in.
    - (**r src in ld_set *)
      rewrite app_nil_r.
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

      apply set_mem_correct1 in Hsrc_in.
      apply set_add_elim in Hsrc_in.
      destruct Hsrc_in as [HF | Hsrc_in].
      { exfalso; apply Hreg_neq; auto. }
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
      remember (setN (encode_sval_fragments Cany32 (Rval (Sreg (ireg_of_breg _))))
         _ astk0) as astk1 eqn: Hastk1_eq.
      simpl.
      unfold anextinstr at 1. repeat abreg_solver_error_prone.
      rewrite HIR12.
      simpl. rewrite Ptrofs.add_zero_l.

      rewrite ptr_int_mul_4.
      rewrite Hdst2.

      rewrite decode_add_r.

      assert (Heq: is_final_state (anextinstr true
         (anextinstr true ars0) # (ireg_of_breg dst) <- (Cval (Vint v_dst))) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq ((anextinstr true
         (anextinstr true ars0) # (ireg_of_breg dst) <- (Cval (Vint v_dst))) IR13)
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

      assert (Hsrc_in_union: In src (set_union breg_eq ld_set st_set)) by  listset_solver.

      specialize (REG_SRC1 Hsrc_in_union).
      destruct REG_SRC1 as (v_src & Hsrc1 & Hsrc2).
      simpl.
      unfold anextinstr, aadd; simpl.
      repeat abreg_solver_error_prone.
      rewrite REG_DST2, Hsrc2 in *.

      assert (Heq: is_final_state (anextinstr_nf true
         (((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize))
           # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
          (aoffset_ptr
             ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize))
              # (ireg_of_breg dst) <- (Cval (Vint v_dst)) PC) wsize))
         # (ireg_of_breg dst) <- (Cval (Val.add (Vint v_dst) (Vint v_src)))) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq ((anextinstr_nf true
         (((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize))
           # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
          (aoffset_ptr
             ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize))
              # (ireg_of_breg dst) <- (Cval (Vint v_dst)) PC) wsize))
         # (ireg_of_breg dst) <- (Cval (Val.add (Vint v_dst) (Vint v_src)))) IR13)
          (Aval (Rval (Sreg IR13))) = false).
        - unfold anextinstr_nf, anextinstr, aundef_flags.
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

      rewrite Hdst1, Hsrc1 in HALU.
      simpl in HALU.
      injection HALU as Heq; subst i.
      eexists; eexists.
      split; [f_equal |].
      constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; repeat abreg_solver.
      + intros.
        specialize (Hfloat _ H).
        repeat float_preg_of_solver.
        repeat (destruct H as [H | H];
            [subst x; auto|]); inversion H.
      + destruct HNoDup as (HNoDup1 & HNoDup2);
        split; repeat apply set_add_nodup; auto.

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
          repeat abreg_solver_error_prone.
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
        rewrite Pregmap.gso. 2:{ unfold ireg_of_breg; intro HF; inversion HF. }
        rewrite Pregmap.gss.
        rewrite HIRPC.
        simpl.
        eexists; f_equal.

      + intros r Hin. repeat listset_solver.

      + unfold match_regs.
        intros.
        specialize (REG r).
        destruct REG as (REG1 & REG2 & REG3).
        destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
        { (**r r = dst *)
          subst r.
          split.
          - intro Hin.
            exists (Int.add v_dst v_src).
            split; repeat abreg_solver.
            simpl; auto.
          - split.
            + intro Hnot_in.
              exfalso.
              apply Hnot_in. listset_solver.
            + intros Hnot_in.
              exfalso.
              apply Hnot_in. listset_solver.
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
              apply Hnot_in. listset_solver.
            + intros Hnot_in.
              assert (Heq: ~ In src st_set) by listset_solver.
              specialize (REG3 Heq); clear Heq.
              destruct REG3 as (vr1 & Hvr3 & Hvr4).
              exists vr1.
              split; repeat abreg_solver.
        }
        { (**r r <> dst /\ r <> src *)
          split.
          - intros.
            assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
            specialize (REG1 Heq); clear Heq.
            destruct REG1 as (vr1 & Hvr1 & Hvr2).
            exists vr1.
            split; repeat abreg_solver.
          - split.
            + intro HN. destruct HN as (HN & HN1).
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
                In r rbpf_arm_callee_save). {
                split; auto. listset_solver.
              }
              specialize (REG2 Heq); clear Heq. repeat abreg_solver.
            + intro HN.
              assert (Heq: ~ In r st_set). {
                intro HF. apply HN. listset_solver.
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
              assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
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
              apply Hin. listset_solver.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso. clear - Hin.
              apply Hin. listset_solver.
            }
            { (**r r <> dst /\ r <> src *) destruct Hin as (Hin & Hin1).
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
                In r rbpf_arm_callee_save). {
                split; auto. listset_solver.
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

      assert (Heq: ~In src ld_set). {
        intro HF; apply Hsrc_in. listset_solver.
      }
      clear Hsrc_in; rename Heq into Hsrc_in.

      assert (Heq: ~ In src st_set) by listset_solver.
      specialize (REG_SRC3 Heq); clear Heq.
      destruct REG_SRC3 as (v_src & Hsrc1 & Hsrc2).

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
      remember (setN (encode_sval_fragments Cany32 (Rval (Sreg (ireg_of_breg _))))
       _ astk0) as astk1 eqn: Hastk1_eq.
      simpl.
      unfold anextinstr at 1. repeat abreg_solver_error_prone.
      rewrite HIR12.
      simpl. rewrite Ptrofs.add_zero_l.

      rewrite ptr_int_mul_4.

      rewrite Hdst2.
      rewrite decode_add_r.
      unfold anextinstr; simpl.

      assert (Heq: is_final_state (((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize)) # 
       (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
      (aoffset_ptr
         ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize)) # 
          (ireg_of_breg dst) <- (Cval (Vint v_dst)) PC) wsize)) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq ((((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize)) # 
       (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
      (aoffset_ptr
         ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize)) # 
          (ireg_of_breg dst) <- (Cval (Vint v_dst)) PC) wsize)) IR13)
          (Aval (Rval (Sreg IR13))) = false).
        - repeat abreg_solver_error_prone.
          rewrite HIR13.
          simpl.
          auto.
        - rewrite Heq.
          rewrite andb_false_r.
          rewrite andb_false_l.
          auto.
      }
      rewrite Heq; clear Heq.


      rewrite decode_str_i_13.
      simpl. repeat abreg_solver_error_prone.
      rewrite HIR13. simpl. rewrite Ptrofs.add_zero_l.

      assert (Heq: ~ In src (set_union breg_eq ld_set st_set) /\
        In src rbpf_arm_callee_save). {
        split; auto. listset_solver.
      }
      specialize (REG_SRC2 Heq); clear Heq.

      remember (((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize)) # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
      (aoffset_ptr ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize)) # (ireg_of_breg dst) <- (Cval (Vint v_dst)) PC)
         wsize)) as asrt eqn: Hasrt_eq.

      erewrite aexec_store_ir13; eauto.
      2:{ subst asrt. repeat abreg_solver_error_prone. assumption. }

      assert (Heq: is_final_state (anextinstr true asrt) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq ((anextinstr true asrt) IR13)
          (Aval (Rval (Sreg IR13))) = false).
        - unfold anextinstr.
          rewrite Hasrt_eq.
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
      remember (setN (encode_sval_fragments Cany32 (Rval (Sreg (ireg_of_breg _))))
       _ astk1) as astk2 eqn: Hastk2_eq.
      simpl.
      unfold anextinstr at 1.
      subst asrt. repeat abreg_solver_error_prone.
      rewrite HIR12.
      simpl. rewrite Ptrofs.add_zero_l.

      rewrite ptr_int_mul_4.

      rewrite Hsrc2.
      assert (Heq: (anextinstr true
           (anextinstr true
              ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize)) # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
              (aoffset_ptr
                 ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize)) # (ireg_of_breg dst) <- (Cval (Vint v_dst)) PC) wsize))
           # (ireg_of_breg src) <- (Cval (Vint v_src)) (ireg_of_breg dst)) = (Cval (Vint v_dst))). {
        unfold anextinstr, aoffset_ptr. repeat abreg_solver.
      }
      rewrite Heq; clear Heq.

      assert (Heq: is_final_state (anextinstr true
         (anextinstr true
            ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize))
             # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
            (aoffset_ptr
               ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize))
                # (ireg_of_breg dst) <- (Cval (Vint v_dst)) PC) wsize))
         # (ireg_of_breg src) <- (Cval (Vint v_src))) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq ((anextinstr true
         (anextinstr true
            ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize))
             # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
            (aoffset_ptr
               ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize))
                # (ireg_of_breg dst) <- (Cval (Vint v_dst)) PC) wsize))
         # (ireg_of_breg src) <- (Cval (Vint v_src))) IR13)
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

      assert (Heq: (anextinstr true
           (anextinstr true
              ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize)) # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
              (aoffset_ptr
                 ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize)) # (ireg_of_breg dst) <- (Cval (Vint v_dst)) PC) wsize))
           # (ireg_of_breg src) <- (Cval (Vint v_src)) (ireg_of_breg src)) = (Cval (Vint v_src))). {
        unfold anextinstr, aoffset_ptr. repeat abreg_solver.
      }
      rewrite Heq; clear Heq.

      simpl.

      assert (Heq: is_final_state (anextinstr_nf true
         (anextinstr true
            (anextinstr true
               ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize))
                # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
               (aoffset_ptr
                  ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize))
                   # (ireg_of_breg dst) <- (Cval (Vint v_dst)) PC) wsize))
            # (ireg_of_breg src) <- (Cval (Vint v_src)))
         # (ireg_of_breg dst) <- (Cval (Vint (Int.add v_dst v_src)))) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq ((anextinstr_nf true
         (anextinstr true
            (anextinstr true
               ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize))
                # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
               (aoffset_ptr
                  ((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize))
                   # (ireg_of_breg dst) <- (Cval (Vint v_dst)) PC) wsize))
            # (ireg_of_breg src) <- (Cval (Vint v_src)))
         # (ireg_of_breg dst) <- (Cval (Vint (Int.add v_dst v_src)))) IR13)
          (Aval (Rval (Sreg IR13))) = false).
        - unfold anextinstr_nf, anextinstr, aundef_flags.
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

      eexists. exists astk2.
      split; [f_equal |].

      constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; simpl; repeat abreg_solver.
      + intros.
        specialize (Hfloat _ H).
        repeat float_preg_of_solver.
        repeat (destruct H as [H | H];
            [subst x; auto|]); inversion H.
      + destruct HNoDup as (HNoDup1 & HNoDup2);
        split; repeat apply set_add_nodup; auto.

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
          repeat abreg_solver_error_prone.
          destruct (ireg_eq IR0 (ireg_of_breg src)) as [Hrs_eq | Hrs_neq].
          { (**r r = src *)
            rewrite <- Hrs_eq.
            repeat abreg_solver_error_prone.
            simpl.
            reflexivity.
          }
          { (**r r <> src *)
            rewrite Pregmap.gso.
            2:{ intro HF. apply Hrs_neq. injection HF as Heq. assumption. }
            repeat abreg_solver_error_prone.
            rewrite Pregmap.gso.
            2:{ intro HF. apply Hr_neq. injection HF as Heq. assumption. }
            repeat abreg_solver.
          }
        }

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

      + destruct HIRPC as (va_pc & HIRPC).
        unfold aoffset_ptr.
        repeat abreg_solver_error_prone.
        rewrite Pregmap.gso. 2:{ unfold ireg_of_breg; intro HF; inversion HF. }
        rewrite Pregmap.gss.
        rewrite Pregmap.gso. 2:{ unfold ireg_of_breg; intro HF; inversion HF. }
        rewrite Pregmap.gss.
        rewrite Pregmap.gso. 2:{ unfold ireg_of_breg; intro HF; inversion HF. }
        rewrite Pregmap.gss.
        rewrite HIRPC.
        simpl.
        eexists; f_equal.

      + intros r Hin. repeat listset_solver.

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
            rewrite <- HALU. rewrite Hsrc1, Hdst1. simpl; auto.
          }
          destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
          { (**r r = src *)
            subst r.
            exists v_src.
            split; repeat abreg_solver.
          }
          { (**r r <> dst /\ r<> src *)
            assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
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
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso; apply HF; clear.
              apply set_union_intro1.
              apply set_add_intro2; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
                In r rbpf_arm_callee_save). {
                split; auto.
                intro Hin; apply HF. listset_solver.
              }
              specialize (REG2 Heq); clear Heq.

              rename HF into Hno_in. repeat abreg_solver.
            }
          }
          { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso; apply HF; clear. listset_solver.
            }
            { (**r r <> dst *)
              assert (Heq: ~ In r st_set). {
                intro Hin; apply HF. listset_solver.
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
            clear - Hdst_callee; apply rbpf_arm_callee_save_reg_ge4; auto.
          - simpl.
            left.
            clear - Hcallee. apply rbpf_arm_callee_save_reg_ge4; auto.
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
              assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
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
              apply Hin. listset_solver.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso. clear - Hin.
              apply Hin. listset_solver.
            }
            { (**r r <> dst /\ r <> src *) destruct Hin as (Hin & Hin1).
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
                In r rbpf_arm_callee_save). {
                split; auto. listset_solver.
              }
              specialize (STK2 Heq); clear Heq. repeat abreg_solver.
            }
        }
    }

    { simpl.

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

      assert (Heq: ~In src ld_set). {
        intro HF; apply Hsrc_in. listset_solver.
      }
      clear Hsrc_in; rename Heq into Hsrc_in.

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

      assert (Heq: is_final_state (anextinstr true
         (anextinstr true ars0) # (ireg_of_breg dst) <- (Cval (Vint v_dst))) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq ((anextinstr true
         (anextinstr true ars0) # (ireg_of_breg dst) <- (Cval (Vint v_dst))) IR13)
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

      unfold aexec_load.
      assert (Heq: (anextinstr true (anextinstr true ars0) #
      (ireg_of_breg dst) <- (Cval (Vint v_dst)) IR12) = ars0 IR12). {
        unfold anextinstr. repeat abreg_solver.
      }
      rewrite Heq; clear Heq.
      rewrite HIR12; simpl.
      rewrite Ptrofs.add_zero_l.
      rewrite ptr_int_mul_4.

      assert (Heq: ~ In src st_set) by listset_solver.
      specialize (REG_SRC3 Heq); clear Heq.
      destruct REG_SRC3 as (v_src & Hsrc1 & Hsrc2).
      rewrite Hsrc2.

      rewrite decode_add_r.
      unfold anextinstr; simpl. repeat abreg_solver_error_prone.
      simpl.

      assert (Heq: is_final_state (anextinstr_nf true
         (((((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize))
             # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
            (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize))
           # (ireg_of_breg src) <- (Cval (Vint v_src))) # PC <-
          (aoffset_ptr (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize) wsize))
         # (ireg_of_breg dst) <- (Cval (Vint (Int.add v_dst v_src)))) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq ((anextinstr_nf true
         (((((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize))
             # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
            (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize))
           # (ireg_of_breg src) <- (Cval (Vint v_src))) # PC <-
          (aoffset_ptr (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize) wsize))
         # (ireg_of_breg dst) <- (Cval (Vint (Int.add v_dst v_src)))) IR13)
          (Aval (Rval (Sreg IR13))) = false).
        - unfold anextinstr_nf, anextinstr, aundef_flags.
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

      assert (Heq: is_final_state (((((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize)) # 
         (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
        (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize))
       # (ireg_of_breg src) <- (Cval (Vint v_src))) # PC <-
      (aoffset_ptr (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize) wsize)) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq ((((((ars0 # PC <- (aoffset_ptr (ars0 PC) wsize)) # 
         (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
        (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize))
       # (ireg_of_breg src) <- (Cval (Vint v_src))) # PC <-
      (aoffset_ptr (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize) wsize)) IR13)
          (Aval (Rval (Sreg IR13))) = false).
        - unfold anextinstr_nf, anextinstr, aundef_flags.
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

      eexists. exists astk1.
      split; [f_equal |].

      constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; simpl; repeat abreg_solver.
      + intros.
        specialize (Hfloat _ H).
        repeat float_preg_of_solver.
        repeat (destruct H as [H | H];
            [subst x; auto|]); inversion H.
      + destruct HNoDup as (HNoDup1 & HNoDup2);
        split; repeat apply set_add_nodup; auto.

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
          repeat abreg_solver_error_prone.
          destruct (ireg_eq IR0 (ireg_of_breg src)) as [Hrs_eq | Hrs_neq].
          { (**r r = src *)
            rewrite <- Hrs_eq.
            repeat abreg_solver_error_prone.
            simpl.
            reflexivity.
          }
          { (**r r <> src *)
            rewrite Pregmap.gso.
            2:{ intro HF. apply Hrs_neq. injection HF as Heq. assumption. }
            repeat abreg_solver_error_prone.
            rewrite Pregmap.gso.
            2:{ intro HF. apply Hr_neq. injection HF as Heq. assumption. }
            repeat abreg_solver.
          }
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

      + intros r Hin. repeat listset_solver.

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
            rewrite <- HALU. rewrite Hsrc1, Hdst1. simpl; auto.
          }
          destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
          { (**r r = src *)
            subst r.
            exists v_src.
            split; repeat abreg_solver.
          }
          { (**r r <> dst /\ r<> src *)
            assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
            specialize (REG1 Heq); clear Heq.
            destruct REG1 as (vr_r & Hvr_r1 & Hvr_r2).
            exists vr_r.
            split; repeat abreg_solver.
          }
        * split; intro HF. destruct HF as (HF & HF1).
          { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso; apply HF; clear. listset_solver.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso; apply HF; clear. listset_solver.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
                In r rbpf_arm_callee_save). {
                split; auto.
                intro Hin; apply HF. listset_solver.
              }
              specialize (REG2 Heq); clear Heq.

              rename HF into Hno_in. repeat abreg_solver.
            }
          }
          { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso; apply HF; clear. listset_solver.
            }
            { (**r r <> dst *)
              assert (Heq: ~ In r st_set). {
                intro Hin; apply HF. listset_solver.
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
              assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
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
              apply Hin. listset_solver.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso. clear - Hin.
              apply Hin. listset_solver.
            }
            { (**r r <> dst /\ r <> src *) destruct Hin as (Hin & Hin1).
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
                In r rbpf_arm_callee_save). {
                split; auto. listset_solver.
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
      rewrite decode_add_r.

      assert (Hsrc_in_union: In src (set_union breg_eq ld_set st_set)). {
        apply set_union_intro1.
        unfold set_In; auto.
      }

      specialize (REG_SRC1 Hsrc_in_union).
      destruct REG_SRC1 as (v_src & Hsrc1 & Hsrc2).

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

      assert (Heq: is_final_state (anextinstr true ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq ((anextinstr true ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) IR13)
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

      simpl.
      unfold anextinstr, aadd; simpl. repeat abreg_solver_error_prone.
      rewrite Hsrc2 in *.

      rewrite Hdst1, Hsrc1 in HALU.

      assert (Heq: is_final_state (anextinstr_nf true
         ((ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
          (aoffset_ptr (ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst)) PC)
             wsize)) # (ireg_of_breg dst) <-
         (Cval (Val.add (Vint v_dst) (Vint v_src)))) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq ((anextinstr_nf true
         ((ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
          (aoffset_ptr (ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst)) PC)
             wsize)) # (ireg_of_breg dst) <-
         (Cval (Val.add (Vint v_dst) (Vint v_src)))) IR13)
          (Aval (Rval (Sreg IR13))) = false).
        - unfold anextinstr_nf, anextinstr, aundef_flags.
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

      simpl in HALU.
      injection HALU as Heq; subst i.
      eexists; eexists.
      split; [f_equal |].
      constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; repeat abreg_solver.
      + intros.
        specialize (Hfloat _ H).
        repeat float_preg_of_solver.
        repeat (destruct H as [H | H];
            [subst x; auto|]); inversion H.
      + destruct HNoDup as (HNoDup1 & HNoDup2);
        split; repeat apply set_add_nodup; auto.

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
          repeat abreg_solver_error_prone.
          rewrite Pregmap.gso.
          2:{ intro HF. apply Hr_neq. injection HF as Heq. assumption. }
          repeat abreg_solver.
        }

      + destruct HIRPC as (va_pc & HIRPC).
        unfold aoffset_ptr.
        repeat abreg_solver_error_prone.
        rewrite Pregmap.gso. 2:{ unfold ireg_of_breg; intro HF; inversion HF. }
        rewrite Pregmap.gss.
        rewrite Pregmap.gso. 2:{ unfold ireg_of_breg; intro HF; inversion HF. }
        rewrite HIRPC.
        simpl.
        eexists; f_equal.

      + intros r Hin. repeat listset_solver.

      + unfold match_regs.
        intros.
        specialize (REG r).
        destruct REG as (REG1 & REG2 & REG3).
        destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
        { (**r r = dst *)
          subst r.
          split.
          - intro Hin.
            exists (Int.add v_dst v_src).
            split; repeat abreg_solver.
            simpl; auto.
          - split.
            + intro Hnot_in.
              exfalso.
              apply Hnot_in. listset_solver.
            + intros Hnot_in.
              exfalso.
              apply Hnot_in. listset_solver.
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
              apply Hnot_in. listset_solver.
            + intros Hnot_in.
              assert (Heq: ~ In src st_set) by listset_solver.
              specialize (REG3 Heq); clear Heq.
              destruct REG3 as (vr1 & Hvr3 & Hvr4).
              exists vr1.
              split; repeat abreg_solver.
        }
        { (**r r <> dst /\ r <> src *)
          split.
          - intros.
            assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
            specialize (REG1 Heq); clear Heq.
            destruct REG1 as (vr1 & Hvr1 & Hvr2).
            exists vr1. split; repeat abreg_solver.
          - split.
            + intro HN. destruct HN as (HN & HN1).
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
                In r rbpf_arm_callee_save). {
                split; auto. listset_solver.
              }
              specialize (REG2 Heq); clear Heq. repeat abreg_solver.
            + intro HN.
              assert (Heq: ~ In r st_set). {
                intro HF. apply HN. listset_solver.
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
              apply STK1. listset_solver.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
              specialize (STK1 Heq); clear Heq.
              apply STK1.
            }
          - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso. clear - Hin.
              apply Hin. listset_solver.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso. clear - Hin.
              apply Hin. listset_solver.
            }
            { (**r r <> dst /\ r <> src *) destruct Hin as (Hin & Hin1).
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
                  In r rbpf_arm_callee_save). {
                split; auto. listset_solver.
              }
              specialize (STK2 Heq); clear Heq. repeat abreg_solver.
            }
        }

  - (**r src not in ld_set *)
    apply set_mem_complete1 in Hsrc_in.

    destruct (set_mem breg_eq src rbpf_arm_callee_save) eqn: Hcallee.
    {
      apply set_mem_correct1 in Hcallee.
      simpl.
      rewrite decode_ldr_i_12.
      simpl.

      rewrite HIR12. simpl. rewrite Ptrofs.add_zero_l.

      assert (Heq: ~In src ld_set). {
        intro HF; apply Hsrc_in. listset_solver.
      }
      clear Hsrc_in; rename Heq into Hsrc_in.
      rewrite ptr_int_mul_4.
      rewrite Hdst2.

      rewrite decode_str_i_13.
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

      assert (Heq: is_final_state (anextinstr true ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq ((anextinstr true ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) IR13)
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

      assert (Heq: (anextinstr true ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst)) IR13) = ars0 IR13). {
        unfold anextinstr. repeat abreg_solver.
      }
      rewrite Heq; clear Heq.
      rewrite HIR13. simpl. rewrite Ptrofs.add_zero_l.

      assert (Heq: ~ In src (set_union breg_eq ld_set st_set) /\
        In src rbpf_arm_callee_save). {
        split; auto. listset_solver.
      }
      specialize (REG_SRC2 Heq); clear Heq.

      erewrite aexec_store_ir13; eauto.
      2:{ unfold anextinstr; simpl. repeat abreg_solver_error_prone. assumption. }

      assert (Heq: is_final_state (anextinstr true
         (anextinstr true ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst)))) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq ((anextinstr true
         (anextinstr true ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst)))) IR13)
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

      assert (Heq: ~ In src st_set) by listset_solver.
      specialize (REG_SRC3 Heq); clear Heq.
      destruct REG_SRC3 as (v_src & Hsrc1 & Hsrc2).

      rewrite ptr_int_mul_4.

      rewrite Hsrc2.
      rewrite decode_add_r.
      unfold anextinstr; simpl. repeat abreg_solver_error_prone.

      simpl.

      assert (Heq: is_final_state (((((ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
         (aoffset_ptr (ars0 PC) wsize)) # PC <-
        (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize))
       # (ireg_of_breg src) <- (Cval (Vint v_src))) # PC <-
      (aoffset_ptr (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize) wsize)) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq ((((((ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
         (aoffset_ptr (ars0 PC) wsize)) # PC <-
        (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize))
       # (ireg_of_breg src) <- (Cval (Vint v_src))) # PC <-
      (aoffset_ptr (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize) wsize)) IR13)
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

      assert (Heq: is_final_state (anextinstr_nf true
         (((((ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
             (aoffset_ptr (ars0 PC) wsize)) # PC <-
            (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize))
           # (ireg_of_breg src) <- (Cval (Vint v_src))) # PC <-
          (aoffset_ptr (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize) wsize))
         # (ireg_of_breg dst) <- (Cval (Vint (Int.add v_dst v_src)))) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq ((anextinstr_nf true
         (((((ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
             (aoffset_ptr (ars0 PC) wsize)) # PC <-
            (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize))
           # (ireg_of_breg src) <- (Cval (Vint v_src))) # PC <-
          (aoffset_ptr (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize) wsize))
         # (ireg_of_breg dst) <- (Cval (Vint (Int.add v_dst v_src)))) IR13)
          (Aval (Rval (Sreg IR13))) = false).
        - unfold anextinstr_nf, anextinstr, aundef_flags.
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

      eexists. exists astk1.
      split; [f_equal |].

      constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; simpl; repeat abreg_solver.
      + intros.
        specialize (Hfloat _ H).
        repeat float_preg_of_solver.
        repeat (destruct H as [H | H];
            [subst x; auto|]); inversion H.
      + destruct HNoDup as (HNoDup1 & HNoDup2);
        split; repeat apply set_add_nodup; auto.

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
          repeat abreg_solver_error_prone.
          destruct (ireg_eq IR0 (ireg_of_breg src)) as [Hrs_eq | Hrs_neq].
          { (**r r = src *)
            rewrite <- Hrs_eq.
            repeat abreg_solver_error_prone.
            simpl.
            reflexivity.
          }
          { (**r r <> src *)
            rewrite Pregmap.gso.
            2:{ intro HF. apply Hrs_neq. injection HF as Heq. assumption. }
            repeat abreg_solver_error_prone.
            rewrite Pregmap.gso.
            2:{ intro HF. apply Hr_neq. injection HF as Heq. assumption. }
            repeat abreg_solver.
          }
        }

      + clear - HAR11 Hastk1_eq.
        unfold astack_load in *.
        destruct Mem.valid_access_dec; [| inversion HAR11].
        subst astk1.
        rewrite ab_getN_setN_outside; [auto | ].
        right. simpl.
        destruct src; simpl; lia.

      + destruct HIRPC as (va_pc & HIRPC).
        unfold aoffset_ptr.
        repeat abreg_solver_error_prone.
        rewrite Pregmap.gso. 2:{ unfold ireg_of_breg; intro HF; inversion HF. }
        rewrite Pregmap.gss.
        rewrite HIRPC.
        simpl.
        eexists; f_equal.

      + intros r Hin. repeat listset_solver.

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
            rewrite <- HALU. rewrite Hsrc1, Hdst1. simpl; auto.
          }
          destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
          { (**r r = src *)
            subst r.
            exists v_src.
            split; repeat abreg_solver.
          }
          { (**r r <> dst /\ r<> src *)
            assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
            specialize (REG1 Heq); clear Heq.
            destruct REG1 as (vr_r & Hvr_r1 & Hvr_r2).
            exists vr_r.
            split; repeat abreg_solver.
          }
        * split; intro HF. destruct HF as (HF & HF1).
          { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso; apply HF; clear. listset_solver.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso; apply HF; clear.
              apply set_union_intro1.
              apply set_add_intro2; auto.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
                In r rbpf_arm_callee_save). {
                split; auto.
                intro Hin; apply HF. listset_solver.
              }
              specialize (REG2 Heq); clear Heq.

              rename HF into Hno_in. repeat abreg_solver.
            }
          }
          { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso; apply HF; clear. listset_solver.
            }
            { (**r r <> dst *)
              assert (Heq: ~ In r st_set). {
                intro Hin; apply HF. listset_solver.
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
              assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
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
              apply Hin. listset_solver.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso. clear - Hin.
              apply Hin. listset_solver.
            }
            { (**r r <> dst /\ r <> src *) destruct Hin as (Hin & Hin1).
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
                In r rbpf_arm_callee_save). {
                split; auto. listset_solver.
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
        intro HF; apply Hsrc_in. listset_solver.
      }
      clear Hsrc_in; rename Heq into Hsrc_in.
      rewrite ptr_int_mul_4.

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
      rewrite Hdst2.
      unfold anextinstr; simpl. repeat abreg_solver_error_prone.

      assert (Heq: is_final_state ((ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
      (aoffset_ptr (ars0 PC) wsize)) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq (((ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
      (aoffset_ptr (ars0 PC) wsize)) IR13)
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

      rewrite HIR12.
      simpl. rewrite Ptrofs.add_zero_l.
      rewrite ptr_int_mul_4.

      assert (Heq: ~ In src st_set). {
        intro HF; apply Hsrc_in. listset_solver.
      }
      specialize (REG_SRC3 Heq); clear Heq.
      destruct REG_SRC3 as (v_src & Hsrc1 & Hsrc2).

      rewrite Hsrc2.

      rewrite decode_add_r.
      unfold anextinstr; simpl. repeat abreg_solver_error_prone.
      simpl.

      assert (Heq: is_final_state ((((ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
        (aoffset_ptr (ars0 PC) wsize)) # (ireg_of_breg src) <-
       (Cval (Vint v_src))) # PC <-
      (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize)) = false). {
        unfold is_final_state.
        assert (Heq: aval_eq (((((ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
        (aoffset_ptr (ars0 PC) wsize)) # (ireg_of_breg src) <-
       (Cval (Vint v_src))) # PC <-
      (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize)) IR13)
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

    assert (Heq: is_final_state (anextinstr_nf true
         ((((ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
            (aoffset_ptr (ars0 PC) wsize)) # (ireg_of_breg src) <-
           (Cval (Vint v_src))) # PC <-
          (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize))
         # (ireg_of_breg dst) <- (Cval (Vint (Int.add v_dst v_src)))) = false). {
      unfold is_final_state.
      assert (Heq: aval_eq ((anextinstr_nf true
         ((((ars0 # (ireg_of_breg dst) <- (Cval (Vint v_dst))) # PC <-
            (aoffset_ptr (ars0 PC) wsize)) # (ireg_of_breg src) <-
           (Cval (Vint v_src))) # PC <-
          (aoffset_ptr (aoffset_ptr (ars0 PC) wsize) wsize))
         # (ireg_of_breg dst) <- (Cval (Vint (Int.add v_dst v_src)))) IR13)
        (Aval (Rval (Sreg IR13))) = false).
      - unfold anextinstr_nf, anextinstr, aundef_flags.
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

      eexists. exists astk0.
      split; [f_equal |].

      constructor; auto; unfold anextinstr_nf, anextinstr, aundef_flags; simpl; repeat abreg_solver.
      + intros.
        specialize (Hfloat _ H).
        repeat float_preg_of_solver.
        repeat (destruct H as [H | H];
            [subst x; auto|]); inversion H.
      + destruct HNoDup as (HNoDup1 & HNoDup2);
        split; repeat apply set_add_nodup; auto.

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
          repeat abreg_solver_error_prone.
          destruct (ireg_eq IR0 (ireg_of_breg src)) as [Hrs_eq | Hrs_neq].
          { (**r r = src *)
            rewrite <- Hrs_eq.
            repeat abreg_solver_error_prone.
            simpl.
            reflexivity.
          }
          { (**r r <> src *)
            rewrite Pregmap.gso.
            2:{ intro HF. apply Hrs_neq. injection HF as Heq. assumption. }
            repeat abreg_solver_error_prone.
            rewrite Pregmap.gso.
            2:{ intro HF. apply Hr_neq. injection HF as Heq. assumption. }
            repeat abreg_solver.
          }
        }

      + destruct HIRPC as (va_pc & HIRPC).
        unfold aoffset_ptr.
        repeat abreg_solver_error_prone.
        rewrite Pregmap.gso. 2:{ unfold ireg_of_breg; intro HF; inversion HF. }
        rewrite Pregmap.gss.
        rewrite HIRPC.
        simpl.
        eexists; f_equal.

      + intros r Hin. repeat listset_solver.

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
            rewrite <- HALU. rewrite Hsrc1, Hdst1. simpl; auto.
          }
          destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
          { (**r r = src *)
            subst r.
            exists v_src.
            split; repeat abreg_solver.
          }
          { (**r r <> dst /\ r<> src *)
            assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
            specialize (REG1 Heq); clear Heq.
            destruct REG1 as (vr_r & Hvr_r1 & Hvr_r2).
            exists vr_r.
            split; repeat abreg_solver.
          }
        * split; intro HF. destruct HF as (HF & HF1).
          { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso; apply HF; clear. listset_solver.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso; apply HF; clear. listset_solver.
            }
            { (**r r <> dst /\ r <> src *)
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
                In r rbpf_arm_callee_save). {
                split; auto.
                intro Hin; apply HF. listset_solver.
              }
              specialize (REG2 Heq); clear Heq.

              rename HF into Hno_in. repeat abreg_solver.
            }
          }
          { destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso; apply HF; clear. listset_solver.
            }
            { (**r r <> dst *)
              assert (Heq: ~ In r st_set). {
                intro Hin; apply HF. listset_solver.
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
              assert (Heq: In r (set_union breg_eq ld_set st_set)) by listset_solver.
              specialize (STK1 Heq); clear Heq.
              rewrite <- STK1. auto.
            }
          - destruct (breg_eq r dst) as [Hr_eq | Hr_neq].
            { (**r r = dst *)
              subst r.
              exfalso. clear - Hin.
              apply Hin. listset_solver.
            }
            destruct (breg_eq r src) as [Hr_eq | Hr_neq_src].
            { (**r r = src *)
              subst r.
              exfalso. clear - Hin.
              apply Hin. listset_solver.
            }
            { (**r r <> dst /\ r <> src *) destruct Hin as (Hin & Hin1).
              assert (Heq: ~ In r (set_union breg_eq ld_set st_set) /\
                In r rbpf_arm_callee_save). {
                split; auto. listset_solver.
              }
              specialize (STK2 Heq); clear Heq. repeat abreg_solver.
            }
        }
      }
  }
Qed.


Lemma exec_alu32_add_r:
  forall (rs0 rs1: regset) (dst src: breg) i ld_set st_set l2 ld_set2 st_set2 l1 jit_blk st_blk
    m1 ars0 astk0 astkb am
    (HALU : Val.add (rs0 dst) (rs0 src) = Vint i)
    (Hsave : jit_call_save_reg dst src ld_set st_set = (l2, ld_set2, st_set2))
    (Hl1 : l2 ++
      [encode_arm32
         (encode_arm32 (if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one)
            (encode_arm32 (int_of_ireg (ireg_of_breg src))
               (encode_arm32
                  (if Int.lt (int_of_breg dst) (Int.repr 8)
                   then int_of_breg dst
                   else Int.sub (int_of_breg dst) (Int.repr 8)) ADD_R_OP 0 3) 3 4) 7 1) NOP_OP 16 16] = l1)
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
  destruct (breg_eq dst src) as [Hreg_eq | Hreg_neq].
  - (**r dst = src *)
    subst src.
    destruct set_mem eqn: Hdst_in in Hl2.
    + (**r dst in ld *)
      rewrite app_nil_l in Hl2.
      eapply exec_alu32_add_r_eq_dst_in_ld_set; eauto.
    + (**r dst not in ld *)
      eapply exec_alu32_add_r_eq_dst_not_in_ld_set; eauto.
  - (**r dst <> src *)
    destruct set_mem eqn: Hdst_in in Hl2.
    + (**r dst in ld *)
      rewrite app_nil_l in Hl2.
      eapply exec_alu32_add_r_neq_dst_in_ld_set; eauto.
    + (**r dst not in ld *)
      eapply exec_alu32_add_r_neq_dst_not_in_ld_set; eauto.
Qed.