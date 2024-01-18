From compcert.lib Require Import Integers Coqlib Maps.
From compcert.common Require Import AST Values Events Globalenvs Memory Memtype Events Smallstep.
From compcert.cfrontend Require Import Ctypes. (*
From compcert.backend Require Import Locations. *)
From compcert.arm Require Import AsmSyntax ABinSem BinDecode BinSyntax Conventions1 Machregs.

From bpf.comm Require Import JITCall.
From bpf.rbpf32 Require Import TSSyntax TSDecode TSSemanticsA JITConfig.
From bpf.jit Require Import Arm32Reg ThumbInsOp ListSetSort ThumbJIT WholeCompiler.
From bpf.jit Require Import ThumbJITLtac ABMemory TSSemanticsB ThumbJITProofLemma0.
From bpf.jit Require Import ThumbDecodeEncodeALU ThumbDecodeEncodeMEM TSSemanticsBproofdef.
(*
From bpf.jit Require Import TSSemanticsBproof0 TSSemanticsBproof1 TSSemanticsBproof2 TSSemanticsBproof3. TSSemanticsBproof4 TSSemanticsBproof5 *)
From bpf.jit Require Import TSSemanticsBproofAux TSSemanticsBproof6.
From Coq Require Import ZArith Lia List ListSet.

Open Scope nat_scope.
Open Scope asm.
Import ListNotations.

Lemma exec_alu32_list_jit_sequence:
  forall l0 l1 rs m rs' m' jit_blk st_blk ld_set st_set ld_set' st_set' ars1 astk1 astkb1 am
    (BLK: st_blk <> jit_blk)
    (HEXEC : exec_alu32_list l0 rs m = Next rs' m')
    (HJIT : jit_sequence l0 ld_set st_set = Some (l1, ld_set', st_set'))
    (HST: match_states jit_blk st_blk ld_set st_set (State rs m) (AState ars1 astk1 astkb1 am)),
      exists ars2 astk2,
        exec_bin_list l1 ars1 astk1 astkb1 am = ANext ars2 astk2 astkb1 am /\
        match_states jit_blk st_blk ld_set' st_set' (State rs' m') (AState ars2 astk2 astkb1 am).
Proof.
  induction l0; simpl; intros.
  - injection HJIT as Heq1 Heq2 Heq3.
    injection HEXEC as Heq4 Heq5.
    subst.
    exists ars1, astk1.
    unfold exec_bin_list.
    destruct is_final_state; auto.
  - destruct a as [| | op dst src | | | | ]; inversion HEXEC.
    clear H0.
    destruct exec_alu32 as [rs1 m1 | ] eqn: Hexe_one; [| inversion HEXEC].
    destruct jit_one as [((lone & ld1) & st1) | ] eqn: Hjit_one in HJIT; [| inversion HJIT].
    destruct jit_sequence as [((l2 & ld2) & st2) | ] eqn: Hjit_sequence in HJIT; [| inversion HJIT].
    injection HJIT as Heq1 Heq2 Heq3.
    subst l1; subst ld_set'; subst st_set'.

    assert (Hexe_lone: exists ars_k astk_k,
      exec_bin_list lone ars1 astk1 astkb1 am = ANext ars_k astk_k astkb1 am /\
      match_states jit_blk st_blk ld1 st1 (State rs1 m1) (AState ars_k astk_k astkb1 am)). {
      clear - Hexe_one Hjit_one HST.

      eapply exec_alu32_jit_one; eauto.
    }

    destruct Hexe_lone as (ars_k & astk_k & Hexek & Hmatchk).

    eapply IHl0 with (jit_blk := jit_blk) (st_blk := st_blk) (rs := rs1) (m := m1)
      in Hjit_sequence as HE; eauto.

    destruct HE as (ars2 & astk2 & He2 & Hst2).
    exists ars2, astk2.

    split; [| auto].
    eapply exec_bin_list_concat; eauto.

Qed.

Lemma exec_bin_list_jit_aux_tail:
  forall l1 rs m jit_blk st_blk ld_set st_set ld_set' st_set'
    ars astk astkb1 am ars1 astk1 am1 l2
    (HE: exec_bin_list l1 ars astk astkb1 am = ANext ars1 astk1 astkb1 am1)
    (HST: match_states jit_blk st_blk ld_set st_set (State rs m) (AState ars1 astk1 astkb1 am1))
    (HL1: exists ars2 astk2 am2,
        exec_bin_list l2 ars1 astk1 astkb1 am1 = ANext ars2 astk2 astkb1 am2 /\
        match_states jit_blk st_blk ld_set' st_set' (State rs m) (AState ars2 astk2 astkb1 am2) /\
        Mem.load Mint32 am2 st_blk 44 = Some (rs BPC) /\
        ars2 IR11 = Aval (Rval (Sreg IR11))),
      exists ars2 astk2 am2,
        exec_bin_list (l1++l2) ars astk astkb1 am = ANext ars2 astk2 astkb1 am2 /\
        match_states jit_blk st_blk ld_set' st_set' (State rs m) (AState ars2 astk2 astkb1 am2) /\
        Mem.load Mint32 am2 st_blk 44 = Some (rs BPC) /\
        ars2 IR11 = Aval (Rval (Sreg IR11)).
Proof.
  intros.
  destruct HL1 as (ars2 & astk2 & am2 & Heq1 & Heq2).
  exists ars2, astk2, am2.
  split; [ | assumption].
  eapply exec_bin_list_concat; eauto.
Qed.

Lemma sort_preserve_match_state:
  forall jit_blk st_blk ld_set st_set rs m ars2 astk2 astkb1 am2,
    match_states jit_blk st_blk ld_set st_set
    (State rs m) (AState ars2 astk2 astkb1 am2) ->
  match_states jit_blk st_blk (sort_listset ld_set) (sort_listset st_set)
    (State rs m) (AState ars2 astk2 astkb1 am2).
Proof.
  intros.
  inversion H; subst.
  constructor; auto.
  - destruct HNoDup as (HNoDup1 & HNoDup2).
    split; apply NoDup_sort_listset; auto.
  - intros r Hin.
    apply In_sort_listset_intro2.
    apply HSUB.
    apply In_sort_listset_intro1; auto.
  - unfold match_regs in *.
    intros.
    specialize (REG r).
    destruct REG as (REG1 & REG2 & REG3).
    split.
    { intros Hin.
      apply REG1.
      apply set_union_elim in Hin.
      destruct Hin as [Hin | Hin].
      - apply set_union_intro1.
        unfold set_In in *.
        apply In_sort_listset_intro1; auto.
      - apply set_union_intro2.
        unfold set_In in *.
        apply In_sort_listset_intro1; auto.
    }

    split.
    { intros Hin.
      apply REG2.
      destruct Hin as (Hin & Hin1).
      split; auto.
      intro HF.
      apply Hin.
      apply set_union_elim in HF.
      destruct HF as [HF | HF].
      - apply set_union_intro1.
        unfold set_In in *.
        apply In_sort_listset_intro2; auto.
      - apply set_union_intro2.
        unfold set_In in *.
        apply In_sort_listset_intro2; auto.
    }

    intro HF.
    apply REG3.
    intro Hin.
    apply HF.
    apply In_sort_listset_intro2; auto.
  - unfold match_stack in *.
    destruct STK as (STK_INIT & STK).
    split; auto.
    intros r Hin.
    specialize (STK r Hin).
    destruct STK as (STK1 & STK2).
    split.
    { intro HF.
      apply STK1.
      apply set_union_elim in HF.
      destruct HF as [HF | HF].
      - apply set_union_intro1.
        unfold set_In in *.
        apply In_sort_listset_intro1; auto.
      - apply set_union_intro2.
        unfold set_In in *.
        apply In_sort_listset_intro1; auto.
    }

    intro HF0.
    apply STK2.
    destruct HF0 as (HF1 & HF2).
    split; auto.
    intro HF.
    apply HF1.
    apply set_union_elim in HF.
    destruct HF as [HF | HF].
    + apply set_union_intro1.
      unfold set_In in *.
      apply In_sort_listset_intro2; auto.
    + apply set_union_intro2.
      unfold set_In in *.
      apply In_sort_listset_intro2; auto.
Qed.


Lemma exec_bin_list_jit_aux:
  forall l1 rs m jit_blk st_blk ld_set st_set
    ars astk astkb1 am ars1 astk1 am1 l_pc l2 v k
    (BLK: st_blk <> jit_blk)
    (HPC: jit_alu32_thumb_pc k = Some l_pc)
    (HST_PC: Mem.load Mint32 am1 st_blk 44%Z = Some (Vint v) /\
      Val.add (Vint v) (Vint (Int.repr (Z.of_nat (k)))) = rs#BPC)
    (HL: l2 = l1 ++ l_pc ++ jit_alu32_thumb_store (sort_listset st_set) ++ jit_alu32_thumb_reset (sort_listset ld_set))
    (HE: exec_bin_list l1 ars astk astkb1 am = ANext ars1 astk1 astkb1 am1)
    (HST: match_states jit_blk st_blk ld_set st_set (State rs m) (AState ars1 astk1 astkb1 am1)),
      exists ars2 astk2 am2,
        exec_bin_list l2 ars astk astkb1 am = ANext ars2 astk2 astkb1 am2 /\
        match_states jit_blk st_blk [] [] (State rs m) (AState ars2 astk2 astkb1 am2) /\
        Mem.load Mint32 am2 st_blk 44 = Some (rs BPC) /\
        ars2 IR11 = Aval (Rval (Sreg IR11)).
Proof.
  intros.
  subst l2.
  eapply exec_bin_list_jit_aux_tail; eauto.

  eapply exec_alu32_list_jit_pc in HPC as Heq; eauto.
  destruct Heq as (ars2 & astk2 & am2 & Hexe2 & Hst2 & Hpc2 & (v_pc & Hir11_2)).
  eapply exec_bin_list_jit_aux_tail; eauto.

  assert (Heq: match_states jit_blk st_blk (sort_listset ld_set) (sort_listset st_set)
    (State rs m) (AState ars2 astk2 astkb1 am2)) by (apply sort_preserve_match_state; auto).
  clear Hst2; rename Heq into Hst2.

  eapply exec_bin_list_jit_store in Hst2; eauto.
  destruct Hst2 as (ars3 & am3 & Hexe3 & Hst3 & Hir11_3 & Hpc3).
  eapply exec_bin_list_jit_aux_tail; eauto.

  unfold jit_alu32_thumb_reset.
  eapply exec_bin_list_jit_reset_11 in Hst3; eauto. (**r we may need Hpc2 later *)

  destruct Hst3 as (ars4 & Hexe4 & Hst4 & Hir11_4).
  eapply exec_bin_list_jit_aux_tail; eauto.
  eapply exec_bin_list_jit_reset in Hst4 as Heq; eauto.
  destruct Heq as (ars5 & Hexe5 & Hst5 & Hir11_5).
  exists ars5. exists astk2. exists am3.
  split; auto.
Qed.

Definition init_arm_register (v0 v1: val) (ars: aregset): Prop :=
  (**r arm registers *)
  ars#IR0 = Cval v0 /\
  ars#IR1 = Cval v1 /\
  ars#IR11 = Aval (Rval (Sreg IR11)) /\
  ars#IR13 = Aval (Sval Ssp Ptrofs.zero) /\
  ars#IR14 = (Aval (Sval (Sreg PC) (Ptrofs.repr 2))) /\
  ars#PC = Cval v0
.

Lemma init_state_prop:
  forall jit_blk st_blk m2 (rs: regset) v0 v1
    (HPERM: Mem.range_perm m2 st_blk 0 state_block_size Cur Writable)
    (HBLK_VALID: Mem.valid_block m2 jit_blk)
    (Hreg_syn: forall r, Mem.load Mint32 m2 st_blk (z_of_breg r * 4) = Some (rs#r))
    (Hpc_syn: Mem.load Mint32 m2 st_blk 44%Z = Some (rs#BPC))
    (Hcopy_to_prop : forall r : breg, Mem.load Mint32 m2 st_blk (z_of_breg r * 4) = Some (rs r)),
    exists ars1 astk1 astkb1 am,
      init_state compcertbin_signature stack_block_size Ptrofs.zero
      [v0; v1] m2 = ANext ars1 astk1 astkb1 am /\
      st_blk <> astkb1 /\
      (forall x : mreg,
         In x float_callee_save_regs ->
         aval_eq (ars1 (preg_of x)) (Aval (Rval (Sreg (preg_of x)))) = true) /\
      (Mem.range_perm am st_blk 0 state_block_size Cur Writable) /\
      (match_memory m2 am jit_blk st_blk astkb1) /\
      (forall r, In r rbpf_arm_callee_save ->
        ars1 (ireg_of_breg r) = Aval (Rval (Sreg (ireg_of_breg r)))) /\
      init_arm_register v0 v1 ars1 /\
      init_arm_stack am astk1 astkb1 /\
      (forall r : breg, Mem.load Mint32 am st_blk (z_of_breg r * 4) = Some (rs#r)) /\
      (Mem.load Mint32 am st_blk 44%Z = Some (rs#BPC)).
Proof.
  intros.
  unfold init_state, compcertbin_signature, stack_block_size; simpl.
  unfold allocframe; simpl.
  destruct Mem.alloc as (m0 & stkb) eqn: Halloc.
  unfold init_regset.
  unfold astack_store.
  change (Ptrofs.unsigned Ptrofs.zero) with 0%Z.
  destruct Mem.valid_access_dec as [HL | HR].
  2:{
    exfalso.
    assert (Heq: Mem.valid_access m0 Many32 stkb 0 Writable). {
      eapply Mem.valid_access_alloc_same with (chunk := Many32) (ofs := 0%Z) in Halloc;
        eauto; simpl; try lia.
      - eapply Mem.valid_access_freeable_any; eauto.
      - eapply Z.divide_0_r; eauto.
    }
    auto.
  }

  unfold encode_aval.
  unfold regset0.
  simpl.

  do 4 eexists.
  split; [auto | ].

  split.
  { intro HF.
    eapply Mem.fresh_block_alloc; eauto.
    rewrite <- HF.
    eapply Mem.valid_access_valid_block with (chunk := Mint32) (ofs := 44%Z); eauto.
    eapply Mem.valid_access_implies with (p1 := Readable); eauto; [| constructor].
    eapply Mem.load_valid_access; eauto.
  }

  split.
  {
    intros.
    unfold incrinstr.
    do 7 (rewrite Pregmap.gso; [ |
      repeat (destruct H as [H | H];
        [subst x; intro HF; inversion HF|]); inversion H ]).
    simpl; auto.
    destruct preg_eq as [HT | HF];
      [simpl; auto| exfalso; apply HF; reflexivity].
  }

  split.
  {
    unfold state_block_size in *.
    unfold Mem.range_perm in *.
    intros.
    specialize (HPERM _ H).
    eapply Mem.perm_alloc_1; eauto.
  }

  split.
  {
    unfold match_memory.
    eapply Mem.alloc_unchanged_on; eauto.
  }

  split.
  {
    intros. unfold incrinstr.
    repeat abreg_solver.
    rewrite Pregmap.gso; [| destruct r; simpl; intro HF; inversion HF].
    rewrite Pregmap.gso; [| destruct r; simpl; intro HF; inversion HF].
    rewrite Pregmap.gso; [| destruct r; simpl; intro HF; inversion HF].
    rewrite Pregmap.gso; [| destruct r; simpl; intro HF; inversion HF].
    rewrite Pregmap.gso; [rewrite Pregmap.gso; [f_equal | ]|];
      intro HF;
      repeat (destruct H as [H | H]; [subst r; simpl in HF; inversion HF |]);
      inversion H.
  }

  split.
  - unfold incrinstr, init_arm_register.
    split; repeat abreg_solver.
    { rewrite Pregmap.gso; [| intro HF; inversion HF].
      repeat abreg_solver.
      rewrite Pregmap.gso; [| intro HF; inversion HF].
      rewrite Pregmap.gso; [| intro HF; inversion HF].
      rewrite Pregmap.gss. f_equal.
    }
    split; repeat abreg_solver.
    { do 5 (rewrite Pregmap.gso; [| intro HF; inversion HF]).
      rewrite Pregmap.gss. f_equal.
    }
    split; repeat abreg_solver.
    { do 6 (rewrite Pregmap.gso; [| intro HF; inversion HF]).
      f_equal.
    }
    split; repeat abreg_solver.
    { rewrite Pregmap.gso; [| intro HF; inversion HF].
      rewrite Pregmap.gso; [| intro HF; inversion HF].
      rewrite Pregmap.gss. f_equal.
    }
    split; repeat abreg_solver.
    { rewrite ! Pregmap.gss. f_equal.
    }
    rewrite ! Pregmap.gss. f_equal.
  - split.
    + unfold init_arm_stack.
      split.
      * unfold astack_load.
        eapply Mem.valid_access_implies with (p2 := Readable) in HL; eauto; [| constructor].
        destruct Mem.valid_access_dec as [HT | HF]. 2:{ exfalso; apply HF; auto. }
        remember ([Amemval (Rval (Sreg IR13)) Cany32 3; Amemval (Rval (Sreg IR13)) Cany32 2;
         Amemval (Rval (Sreg IR13)) Cany32 1; Amemval (Rval (Sreg IR13)) Cany32 0]) as ml eqn: Hml.
        replace (size_chunk_nat Many32) with (List.length ml).
        { assert (Heq: (ZMap.set 3%Z (Amemval (Rval (Sreg IR13)) Cany32 0)
        (ZMap.set 2%Z (Amemval (Rval (Sreg IR13)) Cany32 1)
           (ZMap.set 1%Z (Amemval (Rval (Sreg IR13)) Cany32 2)
              (ZMap.set 0%Z (Amemval (Rval (Sreg IR13)) Cany32 3) (ZMap.init (Cmemval Undef)))))) =
          (setN ml 0%Z (ZMap.init (Cmemval Undef)))).
          - subst ml; simpl; reflexivity.
          - rewrite Heq.
            rewrite ab_getN_setN_same.
            unfold decode_val. subst ml.
            simpl;
            unfold proj_value, rchunk_of_chunk;
            destruct (Coqlib.proj_sumbool (rchunk_eq Cany32 Cany32)) eqn: Heq1;
              [clear Heq1 | inversion Heq1].
            unfold check_value;
            destruct (Coqlib.proj_sumbool (rchunk_eq Cany32 Cany32)) eqn: Heq1;
              [clear Heq1 | inversion Heq1].
            unfold sval_eq, sreg_eq.
            destruct (preg_eq _ _) as [Heq1 | Hneq1];
              [ | exfalso; apply Hneq1; reflexivity];
            simpl; f_equal.
        }
        subst ml; simpl. unfold size_chunk_nat; reflexivity.
      * unfold Mem.range_perm.
        intros.
        eapply Mem.perm_alloc_2 with (k := Cur) in Halloc; eauto.
        eapply Mem.perm_implies; eauto. constructor.
    + split.
      * intros.
        specialize (Hreg_syn r). rewrite <- Hreg_syn.
        eapply Mem.load_alloc_unchanged; eauto.
        eapply Mem.valid_access_valid_block with (chunk := Mint32) (ofs := (z_of_breg r * 4)%Z).
        eapply Mem.valid_access_implies with (p1 := Readable); eauto; [| constructor].
        eapply Mem.load_valid_access; eauto.
      * rewrite <- Hpc_syn.
        eapply Mem.load_alloc_unchanged; eauto.
        eapply Mem.valid_access_valid_block with (chunk := Mint32) (ofs := 44%Z).
        eapply Mem.valid_access_implies with (p1 := Readable); eauto; [| constructor].
        eapply Mem.load_valid_access; eauto.
Qed.

Lemma exec_bin_list_jit_pre:
  forall ofs m (ars1: aregset) astk1 astkb am jit_blk st_blk (rs: regset)
    (BLK_neq : st_blk <> jit_blk)
    (Hblk_neq : st_blk <> astkb)
    (REG_INV: forall r, exists vi, rs#r = Vint vi)
    (Hfloat: forall x : mreg,
         In x float_callee_save_regs ->
         aval_eq (ars1 (preg_of x)) (Aval (Rval (Sreg (preg_of x)))) = true)
    (HMST: match_memory m am jit_blk st_blk astkb)
    (Hperm_state_blk : Mem.range_perm am st_blk 0 state_block_size Cur Writable)
    (Hcallee: forall r, In r rbpf_arm_callee_save ->
        ars1 (ireg_of_breg r) = Aval (Rval (Sreg (ireg_of_breg r))))
    (Hcopy_to_prop : forall r : breg, Mem.load Mint32 am st_blk (z_of_breg r * 4) = Some (rs r))
    (HPC: Mem.load Mint32 am st_blk 44%Z = Some (rs#BPC))
    (REG: init_arm_register (Vptr jit_blk ofs) (Vptr st_blk Ptrofs.zero) ars1)
    (STK: init_arm_stack am astk1 astkb),
    exists ars2 astk2,
      exec_bin_list jit_alu32_pre ars1 astk1 astkb am = ANext ars2 astk2 astkb am /\
      match_states jit_blk st_blk [] [] (State rs m) (AState ars2 astk2 astkb am).
Proof.
  unfold init_arm_register, init_arm_stack, jit_alu32_pre; simpl; intros.
  rewrite decode_mov_12_1.
  simpl.
  unfold jit_alu32_thumb_mem_template_jit.
  rewrite decode_str_i_13_11.
  simpl.
  unfold aexec_store, aexec_store'; simpl.
  unfold anextinstr_nf, anextinstr, aundef_flags; simpl. repeat abreg_solver_error_prone.
  destruct REG as (REG0 & REG1 &REG11 & REG13 & REG14 & REG15).
  rewrite REG13.
  simpl.
  rewrite Pregmap.gso; [| intro HF; inversion HF].
  rewrite REG11.
  rewrite Ptrofs.add_zero_l.
  replace (Ptrofs.unsigned (Ptrofs.of_int (Int.repr 44))) with 44%Z by reflexivity.
  unfold astack_store.
  destruct STK as (STK & HPERM).
  destruct Mem.valid_access_dec as [HT | HF].
  2:{ exfalso. apply HF.
    unfold Mem.range_perm in HPERM.
    unfold Mem.valid_access.
    split; [| unfold align_chunk;
      replace 44%Z with (11*4)%Z by reflexivity; apply Z.divide_factor_r].
    unfold size_chunk, Mem.range_perm.
    intros.
    apply HPERM.
    unfold stack_block_size. lia.
  }

  simpl.
  remember ([Amemval (Rval (Sreg IR11)) Cany32 3; Amemval (Rval (Sreg IR11)) Cany32 2;
   Amemval (Rval (Sreg IR11)) Cany32 1; Amemval (Rval (Sreg IR11)) Cany32 0]) as ml eqn: Hml.
  assert (Heq: (ZMap.set 47%Z (Amemval (Rval (Sreg IR11)) Cany32 0)
  (ZMap.set 46%Z (Amemval (Rval (Sreg IR11)) Cany32 1)
     (ZMap.set 45%Z (Amemval (Rval (Sreg IR11)) Cany32 2)
        (ZMap.set 44%Z (Amemval (Rval (Sreg IR11)) Cany32 3) astk1)))) =
    (setN ml 44%Z astk1)).
    { subst ml; simpl. reflexivity. }
  rewrite Heq; clear Heq.

    assert (Heq: is_final_state ars1 = false). {
      unfold is_final_state.
      assert (Heq: aval_eq (ars1 IR13) (Aval (Rval (Sreg IR13))) = false).
      - rewrite REG13.
        simpl.
        auto.
      - rewrite Heq.
        rewrite andb_false_r.
        rewrite andb_false_l.
        auto.
    }
    rewrite Heq; clear Heq.

    assert (Heq: is_final_state ((fun r : PregEq.t =>
       match r with
       | CR _ => Cval Vundef
       | _ => ars1 # IR12 <- (ars1 IR1) r
       end) # PC <- (aoffset_ptr (ars1 PC) wsize)) = false). {
      unfold is_final_state.
      assert (Heq: aval_eq (((fun r : PregEq.t =>
       match r with
       | CR _ => Cval Vundef
       | _ => ars1 # IR12 <- (ars1 IR1) r
       end) # PC <- (aoffset_ptr (ars1 PC) wsize)) IR13) (Aval (Rval (Sreg IR13))) = false).
      - repeat abreg_solver_error_prone.
        rewrite Pregmap.gso; [| intro HF; inversion HF].
        rewrite REG13.
        simpl.
        auto.
      - rewrite Heq.
        rewrite andb_false_r.
        rewrite andb_false_l.
        auto.
    }
    rewrite Heq; clear Heq.

    assert (Heq: is_final_state (((fun r : PregEq.t =>
        match r with
        | CR _ => Cval Vundef
        | _ => ars1 # IR12 <- (ars1 IR1) r
        end) # PC <- (aoffset_ptr (ars1 PC) wsize)) # PC <-
      (aoffset_ptr
         ((fun r : PregEq.t =>
           match r with
           | CR _ => Cval Vundef
           | _ => ars1 # IR12 <- (ars1 IR1) r
           end) # PC <- (aoffset_ptr (ars1 PC) wsize) PC) wsize)) = false). {
      unfold is_final_state.
      assert (Heq: aval_eq ((((fun r : PregEq.t =>
        match r with
        | CR _ => Cval Vundef
        | _ => ars1 # IR12 <- (ars1 IR1) r
        end) # PC <- (aoffset_ptr (ars1 PC) wsize)) # PC <-
      (aoffset_ptr
         ((fun r : PregEq.t =>
           match r with
           | CR _ => Cval Vundef
           | _ => ars1 # IR12 <- (ars1 IR1) r
           end) # PC <- (aoffset_ptr (ars1 PC) wsize) PC) wsize)) IR13) (Aval (Rval (Sreg IR13))) = false).
      - repeat abreg_solver_error_prone.
        rewrite Pregmap.gso; [| intro HF; inversion HF].
        rewrite REG13.
        simpl.
        auto.
      - rewrite Heq.
        rewrite andb_false_r.
        rewrite andb_false_l.
        auto.
    }
    rewrite Heq; clear Heq.


  eexists; eexists. split; [reflexivity|].

  constructor; auto; repeat abreg_solver.
  - intros.
    specialize (Hfloat _ H).
    repeat float_preg_of_solver.
    repeat (destruct H as [H | H];
        [subst x; auto|]); inversion H.
  - split; constructor.
  - repeat abreg_solver_error_prone.
    rewrite Pregmap.gso.
    2:{ intro HF. inversion HF. }
    rewrite REG0.
    simpl. auto.

  - unfold astack_load.
    destruct Mem.valid_access_dec as [HF | HF].
    2:{ exfalso; apply HF.
      eapply Mem.valid_access_implies; eauto. constructor.
    }

    replace (size_chunk_nat Many32) with (List.length ml) by
      (subst ml; unfold size_chunk_nat; auto).
    rewrite ab_getN_setN_same.
    unfold decode_val. subst ml.
    simpl;
    unfold proj_value, rchunk_of_chunk;
    destruct (Coqlib.proj_sumbool (rchunk_eq Cany32 Cany32)) eqn: Heq1;
      [clear Heq1 | inversion Heq1].
    unfold check_value;
    destruct (Coqlib.proj_sumbool (rchunk_eq Cany32 Cany32)) eqn: Heq1;
      [clear Heq1 | inversion Heq1].
    unfold sval_eq, sreg_eq.
    destruct (preg_eq _ _) as [Heq1 | Hneq1];
      [ | exfalso; apply Hneq1; reflexivity];
    simpl; f_equal.

  - unfold aoffset_ptr.
    repeat abreg_solver_error_prone.
    rewrite REG15.
    simpl.
    eexists; f_equal.

  - rewrite Pregmap.gss.
    unfold match_regs.
    intros.
    split.
    + intros.
      apply set_union_elim in H.
      destruct H; inversion H.
    + split.
      {
        intros.
        destruct H as (_ & H).
        simpl in H.
        specialize (Hcallee _ H).
        rewrite Pregmap.gso; [| intro HF; inversion HF].
        rewrite Pregmap.gso; [| intro HF; inversion HF].
        rewrite Pregmap.gso; [| destruct r; simpl; intro HF; inversion HF].
        auto.
      }
      intros.
      specialize (Hcopy_to_prop r).
      specialize (REG_INV r).
      destruct REG_INV as (vr & REG_INV).
      exists vr.
      split; auto.
      rewrite <- REG_INV. auto.
  - unfold match_stack.
    split.
    + unfold init_arm_stack.
      split; auto.
      rewrite <- STK.
      unfold astack_load.
      destruct Mem.valid_access_dec as [HF | HF]; [| reflexivity].
      replace (size_chunk_nat Many32) with (List.length ml) by
        (subst ml; unfold size_chunk_nat; auto).
      rewrite ab_getN_setN_outside; [auto|].
      subst ml; simpl; lia.
    + intros.
      split.
      {
        intros.
        apply set_union_elim in H0.
        destruct H0; inversion H0.
      }
      intros.
      repeat abreg_solver.
      rewrite Pregmap.gso; [| destruct r; simpl; intro HF; inversion HF].
      destruct H0 as (_ & H0).
      simpl in H0.
      specialize (Hcallee _ H0).
      auto.
Qed.

Lemma exec_bin_list_jit_post:
  forall l (ars1 ars2: aregset) astk1 astkb am1 astk2 am2 jit_blk st_blk rs m
  (Hir11_4 : ars2 IR11 = Aval (Rval (Sreg IR11)))
  (Hexe_bl : exec_bin_list l ars1 astk1 astkb am1 = ANext ars2 astk2 astkb am2)
  (Hst : match_states jit_blk st_blk [] [] (State rs m) (AState ars2 astk2 astkb am2)),
    exists ars3 astk3,
      exec_bin_list jit_alu32_post ars2 astk2 astkb am2 = ANext ars3 astk3 astkb am2 /\
      is_final_state ars3 = true /\
      get_result_bool AST.Tint (ars3 IR0) = true.
Proof.
  unfold jit_alu32_post; simpl; intros.
  unfold jit_alu32_thumb_mem_template_jit.
  rewrite decode_ldr_i_13_13.
  rewrite decode_bx.
  unfold aexec_instr; simpl.
  inversion Hst; subst.
  rewrite HIR13.
  simpl.
  rewrite Ptrofs.add_zero_l.
  change (Ptrofs.unsigned (Ptrofs.of_int Int.zero)) with 0%Z.
  unfold match_stack in STK.
  destruct STK as (INIT_STK & STK).
  unfold init_arm_stack in INIT_STK.
  destruct INIT_STK as (Hsp & Hperm).
  rewrite Hsp.

    assert (Heq: is_final_state ars2 = false). {
      unfold is_final_state.
      assert (Heq: aval_eq (ars2 IR13) (Aval (Rval (Sreg IR13))) = false).
      - rewrite HIR13.
        simpl.
        auto.
      - rewrite Heq.
        rewrite andb_false_r.
        rewrite andb_false_l.
        auto.
    }
    rewrite Heq; clear Heq.

    assert (Heq: is_final_state (anextinstr true ars2 # IR13 <- (Aval (Rval (Sreg IR13)))) = false). {
      unfold is_final_state.
      assert (Heq: aval_eq
  (anextinstr true ars2 # IR13 <- (Aval (Rval (Sreg IR13))) PC)
  (Aval (Sval (Sreg PC) (Ptrofs.repr 2))) = false).
      - unfold anextinstr.
        repeat abreg_solver_error_prone.
        rewrite Pregmap.gso; [| intro HF; inversion HF].
        destruct HIRPC as (va_pc & HIRPC).
        rewrite HIRPC.
        simpl.
        auto.
      - rewrite Heq.
        rewrite andb_false_l.
        auto.
    }
    rewrite Heq; clear Heq.

  eexists; eexists.
  split; [destruct is_final_state; reflexivity| ].

  unfold is_final_state, anextinstr.
  repeat abreg_solver_error_prone.

  split.
  2:{ abreg_solver. }

  apply andb_true_iff.
  split.
  {
    apply andb_true_iff.
    split.
    - rewrite HIR14.
      simpl.
      auto.
    - simpl; auto.
  }
  rewrite forallb_app.
  apply andb_true_iff.
  rewrite ! forallb_forall.
  split.
  2:{
    intros.
    simpl in H.
    specialize (Hfloat _ H).
    do 3 (rewrite Pregmap.gso; [ |
      repeat (destruct H as [H | H];
        [subst x; intro HF; inversion HF|]); inversion H ]).
    auto.
  }

  intros.
  simpl in H.
  do 3 (rewrite Pregmap.gso; [ |
    repeat (destruct H as [H | H];
      [subst x; intro HF; inversion HF|]); inversion H ]).

  assert (Heq: forall r, In r rbpf_arm_callee_save ->
    aval_eq (ars2 (ireg_of_breg r)) (Aval (Rval (Sreg (ireg_of_breg r)))) = true). {
    intros.
    specialize (STK _ H0).
    destruct STK as (_ & STK).
    rewrite STK. apply aval_eq_refl; auto.
    split; auto.
  }
  clear STK; rename Heq into STK.

  clear - Hir11_4 H STK.
  destruct H as [H | H]; [subst x; simpl | ].
  { specialize (STK R4); simpl in *; apply STK; left; auto. }
  destruct H as [H | H]; [subst x; simpl | ].
  { specialize (STK R5); simpl in *; apply STK; right; left; auto. }
  destruct H as [H | H]; [subst x; simpl | ].
  { specialize (STK R6); simpl in *; apply STK; right; right; left; auto. }
  destruct H as [H | H]; [subst x; simpl | ].
  { specialize (STK R7); simpl in *; apply STK; do 3 right; left; auto. }
  destruct H as [H | H]; [subst x; simpl | ].
  { specialize (STK R8); simpl in *; apply STK; do 4 right; left; auto. }
  destruct H as [H | H]; [subst x; simpl | ].
  { specialize (STK R9); simpl in *; apply STK; do 5 right; left; auto. }
  destruct H as [H | H]; [subst x; simpl | ].
  { specialize (STK R10); simpl in *; apply STK; do 6 right; left; auto. }
  destruct H as [H | H]; [subst x; simpl | inversion H].
  rewrite Hir11_4.
  apply aval_eq_refl; auto.
Qed.

Lemma exec_alu32_list_pc_length:
  forall l rs m rs' m'
    (REG_INV: forall r, exists vi, rs#r = Vint vi)
    (HJITMAX: List.length l <= MAX_BPF_LIST_INPUT)
    (HEXEC : exec_alu32_list l rs m = Next rs' m'),
      rs'#BPC = Val.add rs#BPC (Vint (Int.repr (Z.of_nat (List.length l)))).
Proof.
  unfold MAX_BPF_LIST_INPUT.
  induction l; simpl; intros.
  - injection HEXEC as Hrs_eq Hm_eq; subst.
    unfold Val.add.
    specialize (REG_INV BPC).
    destruct REG_INV as (vi & Heq); rewrite Heq.
    fold Int.zero.
    rewrite Int.add_zero.
    reflexivity.
  - destruct a; inversion HEXEC. clear H0.
    unfold exec_alu32 in HEXEC.
    unfold nextinstr in HEXEC.
    destruct eval_alu32 as [v|] eqn: Hexe_one; [| inversion HEXEC].
    destruct v; inversion HEXEC.
    eapply IHl in HEXEC; eauto.
    + rewrite HEXEC.
      specialize (REG_INV BPC).
      destruct REG_INV as (v_pc & Heq).
      rewrite BPregmap.gss.
      rewrite BPregmap.gso; [| intro HF; inversion HF].
      rewrite ! Heq.
      unfold Vone.
      unfold Val.add.
      f_equal.
      rewrite Int.add_assoc.
      f_equal.
      unfold Int.add, Int.one.
      f_equal.
      replace (Int.unsigned (Int.repr 1)) with 1%Z by reflexivity.
      rewrite Int.unsigned_repr.
      * lia.
      * replace Int.max_unsigned with 4294967295%Z by reflexivity.
        lia.
    + intros.
      specialize (REG_INV r).
      destruct REG_INV as (vi & Heq).
      destruct (bpreg_eq BPC r) as [Hr_eq| Hr_neq].
      * subst r.
        rewrite BPregmap.gss.
        rewrite BPregmap.gso; [| intro HF; inversion HF].
        rewrite Heq.
        unfold Vone.
        simpl.
        eexists; reflexivity.
      * rewrite BPregmap.gso; [| auto].
        destruct (bpreg_eq b r) as [Hb_eq| Hb_neq].
        { subst r.
          rewrite BPregmap.gss.
          exists i; reflexivity.
        }
        {
          exists vi.
          rewrite BPregmap.gso; auto.
        }
    + lia.
Qed.

Lemma exec_alu32_list_jit_alu32_exec_bin_code:
  forall l0 l1 rs m rs' m' ofs jit_blk
    (REG_INV: forall r, exists vi, rs#r = Vint vi)
    (HJITMAX: List.length l0 <= MAX_BPF_LIST_INPUT)
    (HBLK_VALID: Mem.valid_block m jit_blk)
    (HEXEC : exec_alu32_list l0 rs m = Next rs' m')
    (HJIT : jit_alu32 l0 = Some l1),
      exec_bin_code l1 ofs jit_blk rs m = Next rs' m'.
Proof.
  unfold jit_alu32, exec_bin_code.
  intros.
  destruct jit_alu32_aux as [bl | ] eqn: Haux; [| inversion HJIT].
  (**r I don't want to use injection as it will do simpl *)
  apply some_some_same in HJIT.
  destruct Mem.alloc as (m1 & st_blk) eqn: Halloc.
  unfold jit_sequence in HJIT.
  eapply copy_to_prop in Halloc as Heq; eauto.

  assert (HBLK_VALID1: Mem.valid_block m1 jit_blk) by
    (eapply Mem.valid_block_alloc; eauto).

  assert (BLK_neq: st_blk <> jit_blk). {
    apply Mem.fresh_block_alloc in Halloc.
    intro HF.
    apply Halloc.
    rewrite HF.
    auto.
  }

  destruct Heq as (m2 & Hcopy_to & Hvalid_blk & Hcopy_to_prop & Hpc_syn & Hperm_state_blk).
  rewrite Hcopy_to.
  eapply init_state_prop with
    (v0 := Val.add (Vptr jit_blk Ptrofs.zero)
      (Vint (Int.repr (Z.of_nat (4 * ofs)))))
    (v1 := Vptr st_blk Ptrofs.zero) in Hcopy_to_prop as Hinit_state; eauto.
  destruct Hinit_state as (ars1 & astk1 & astkb1 & am &
    Hinit_state & Hblk_neq & Hfloat & Hperm1 & HMST & Hcallee & Hinit_reg &
    Hinit_stack & Hreg_syn_arm & Hpc_syn_arm).
  rewrite Hinit_state.

  unfold jit_alu32_aux in Haux.
  destruct jit_sequence as [((cl & ld_set) & st_set) |] eqn: Hseq; [| inversion Haux].
  destruct cl eqn: HL; [inversion Haux| ].
  rewrite <- HL in *.
  destruct jit_alu32_thumb_pc as [l_pc |] eqn: Hl_pc; [| inversion Haux].
  injection Haux as Heq; subst bl.

  subst l1.

  (**r do jit_alu32_pre *)
  eapply exec_bin_list_jit_pre with (jit_blk := jit_blk) in Hinit_reg as Heq; eauto.

  destruct Heq as (ars2 & astk2 & Hexe_pre & Hst1).

  (**r do jit *)
  apply exec_alu32_list_same_mem in HEXEC as Hm_eq; eauto; subst m'.
  apply exec_alu32_list_change_mem with (m1 := m2) in HEXEC as Hexe1; eauto.

  eapply exec_alu32_list_jit_sequence with (st_blk := st_blk) (jit_blk := jit_blk)
    (ld_set := []) (st_set := []) (ars1 := ars2) (astk1 := astk2)
    (astkb1 := astkb1) (am := am) in Hexe1 as Heq; eauto.
  destruct Heq as (ars3 & astk3 & Hexe_bl & Hst3).
  (**r we should say:
    - rs#BPC = rs'#BPC+List.length l0 and 
    - Hreg_syn_arm + Hpc_syn_arm: rs = st_blk *)
  apply exec_alu32_list_pc_length in Hexe1 as Hpc_eq; auto.

  specialize (REG_INV BPC) as Hpc_eq1.
  destruct Hpc_eq1 as (v_pc & Hpc_eq1); rewrite Hpc_eq1 in *.

  eapply exec_bin_list_jit_aux in Hst3 as Heq; eauto.

  destruct Heq as (ars4 & astk4 & am4 & Hexe_ldst & Hst4 & Hpc & Hir11_4).

  (**r do jit_alu32_post *)
  eapply exec_bin_list_jit_post in Hexe_ldst as Heq; eauto.
  destruct Heq as (ars5 & astk5 & Hexe_post & Hfinal_state & Hget_result).

  erewrite exec_bin_list_concat with
    (ars1 := ars2) (astk1 := astk2) (astkb1 := astkb1) (m1 := am)
    (ars' := ars5) (astk' := astk5) (astkb' := astkb1) (m' := am4); eauto.
  - rewrite Hfinal_state.
    rewrite Hget_result.
    assert (Heq: forall r : breg, Mem.load Mint32 am4 st_blk (z_of_breg r * 4) = Some (rs' r)). {
      clear - Hst4.
      inversion Hst4.
      clear - REG.
      unfold match_regs in REG.
      intros.
      specialize (REG r).
      destruct REG as (_ & _ & REG).
      assert (HT: ~ In r []) by (intro HF; inversion HF).
      specialize (REG HT).
      destruct REG as (vr & Heq1 & Heq2).
      rewrite Heq1. auto.
    }
    inversion Hst4; subst.
    clear - Hpc Heq HPERM.
    erewrite copy_from_prop; eauto.
  - erewrite exec_bin_list_concat with
      (ars1 := ars4) (astk1 := astk4) (astkb1 := astkb1) (m1 := am4)
      (ars' := ars5) (astk' := astk5) (astkb' := astkb1) (m' := am4); eauto.
Qed.

Section JITForwardSimulationProof1.

Hypothesis _bpf_get_call: ident -> genv -> option fundef.
Hypothesis memory_region_map: block -> val -> Prop.

Definition valid_block_state (st: state) (b: block): Prop :=
  match st with
  | State _ m => Mem.valid_block m b
  end.

Theorem bstep_forward_simulation:
  forall ge bpf_get_call mem_map c bl jit_blk rs0 m0 t rs1 m1 kl l kv,
    astep bpf_get_call mem_map c kl ge (State rs0 m0) t (State rs1 m1) ->
    reg_inv (State rs0 m0) ->
    List.length c <= MAX_BPF_LIST_INPUT ->
    (forall ep l1, In (ep, l1) kl -> List.length l1 <= MAX_BPF_LIST_INPUT) ->
    valid_block_state (State rs0 m0) jit_blk ->
    combiner kl = Some bl ->
    concat_bin bl = (kv, l) ->
    code_subset_blk l 0 jit_blk (State rs0 m0) = true ->
      star (bstep bpf_get_call mem_map c bl jit_blk) ge (State rs0 m0) t (State rs1 m1).
Proof.
  induction 1.
  - (**r exec_step_alu32 *)
    rename H into HPC.
    rename H0 into Hfind.
    rename H1 into Hnth.
    rename H2 into HEXEC.
    intros HREG_INV HL_INV HLK_INV HValid HC HL HSUB.

    (* eapply exec_alu32_list_reg_inv in HREG_INV; eauto. *)
    simpl in HSUB.
    eapply combiner_nth_error in HC as Heq; eauto.

    apply nth_error_In in Hnth as Hin.
    specialize (HLK_INV _ _ Hin).

    destruct Heq as (ofs & l1 & HIN & HOFS & HJIT).
    eapply star_one; eapply bexec_step_alu32
      with (v := v) (n := n) (ofs := ofs) (l := l1); auto.
    + eapply Hfind.
    + eapply code_subset_in_blk_in; eauto.
    + eapply exec_alu32_list_jit_alu32_exec_bin_code; eauto.
  - intros; eapply star_one; eapply bexec_step_jmp_always; eauto.
  - intros; eapply star_one; eapply bexec_step_jmp_cond; eauto.
  - intros; eapply star_one; eapply bexec_step_internal_load; eauto.
  - intros; eapply star_one; eapply bexec_step_internal_store; eauto.
  - intros; eapply star_one; eapply bexec_step_external; eauto.
Qed.

End JITForwardSimulationProof1.