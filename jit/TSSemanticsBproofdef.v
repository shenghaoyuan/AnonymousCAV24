From compcert.lib Require Import Integers Coqlib Maps.
From compcert.common Require Import AST Values Memory.
From compcert.arm Require Import AsmSyntax ABinSem BinDecode BinSyntax Conventions1 Machregs.

From bpf.comm Require Import JITCall.
From bpf.rbpf32 Require Import TSSyntax JITConfig TSSemanticsA.
From bpf.jit Require Import Arm32Reg ABMemory ThumbJITProofLemma0.

From Coq Require Import ZArith Lia List ListSet.

Open Scope nat_scope.
Open Scope asm.
Import ListNotations.

Inductive astate: Type := AState: aregset -> astack -> block -> mem -> astate.

Definition match_regs (rs: regset) (ars: aregset)
  (ld_set st_set: listset) (st_blk: block) (m: mem): Prop :=
  forall r,
    (**r if a bpf register is recorded in history,
        - it value is 32-bit and 
        - the related arm register has the same concrete value *)
    (List.In r (set_union breg_eq ld_set st_set) ->
      exists vr, rs#r = (Vint vr)  /\ ars (ireg_of_breg r) = Cval (Vint vr)) /\
    (**r if a bpf register is not recorded in history,
        - the related arm register has the original abstract value *)
    ((~List.In r (set_union breg_eq ld_set st_set)) /\ List.In r rbpf_arm_callee_save  ->
      ars (ireg_of_breg r) = Aval (Rval (Sreg (ireg_of_breg r)))) /\
    (**r if a bpf register is not recorded in history,
        - it value is 32-bit and
        - the related cells in state_block has the same value *)
    (~(List.In r st_set) ->
      exists vr, rs#r = (Vint vr) /\ Mem.load Mint32 m st_blk
      (z_of_breg r * 4) = Some (Vint vr))
.

Definition init_arm_stack (am: mem) (astk: astack) (astkb: block): Prop :=
  astack_load Many32 am astk astkb 0%Z = Some (Aval (Rval (Sreg IR13))) /\
  Mem.range_perm am astkb 0%Z stack_block_size Cur Writable.

Definition match_stack (ars: aregset) (ld_set st_set: listset)
  (stk:astack) (stkb: block) (m: mem): Prop :=
  init_arm_stack m stk stkb /\
  forall r, List.In r rbpf_arm_callee_save ->
    (List.In r (set_union breg_eq ld_set st_set) ->
          astack_load Many32 m stk stkb (z_of_breg r * 4) =
            Some (Aval (Rval (Sreg (ireg_of_breg r))))) /\
    (~List.In r (set_union breg_eq ld_set st_set) /\ List.In r rbpf_arm_callee_save ->
      (ars (ireg_of_breg r)) = (Aval (Rval (Sreg (ireg_of_breg r)))))
.

Definition match_memory (m0 m1: mem) (jit_blk st_blk stkb: block): Prop :=
  Mem.unchanged_on (fun b _ => (*b <> jit_blk /\ *) b <> st_blk /\ b <> stkb) m0 m1.

Inductive match_states (jit_blk st_blk : block) (ld_set st_set: listset): state -> astate -> Prop :=
| match_states_intro: forall rs (ars: aregset) astk astkb m am
  (Hfloat: forall x : mreg,
         In x float_callee_save_regs ->
         aval_eq (ars (preg_of x)) (Aval (Rval (Sreg (preg_of x)))) = true)
  (BLK: st_blk <> jit_blk /\ st_blk <> astkb)
  (HPERM: Mem.range_perm am st_blk 0%Z state_block_size Cur Writable)
  (HNoDup: NoDup ld_set /\ NoDup st_set)
  (HAR0: get_result_bool AST.Tint (ars#IR0) = true)
  (HAR11: astack_load Many32 am astk astkb 44%Z = Some (Aval (Rval (Sreg IR11))))
  (HIR12: ars#IR12 = Cval (Vptr st_blk Ptrofs.zero))
  (HIR13: ars#IR13 = Aval (Sval Ssp Ptrofs.zero))
  (HIR14: ars#IR14 = (Aval (Sval (Sreg PC) (Ptrofs.repr 2))))
  (HIRPC: exists va_pc, ars#PC = Cval (Vptr jit_blk va_pc))
  (HSUB: forall r, List.In r st_set -> List.In r ld_set) (**r opt *)
  (REG: match_regs rs ars ld_set st_set st_blk am)
  (STK: match_stack ars ld_set st_set astk astkb am)
  (MEM: match_memory m am jit_blk st_blk astkb)
  ,
    match_states jit_blk st_blk ld_set st_set
      (State rs m) (AState ars astk astkb am).

Lemma rbpf_arm_callee_save_reg_ge4:
  forall dst
  (HD : @set_In breg dst rbpf_arm_callee_save),
    (4 <= z_of_breg dst * 4)%Z.
Proof.
  intros.
  simpl in HD.
  destruct dst; simpl in *; try lia.
  repeat (destruct HD as [HD | HD]; [inversion HD | ]).
  inversion HD.
Qed.

Ltac init_arm_stack_update1 :=
  match goal with
  | STK1 : @eq (option aval) (astack_load Many32 ?am ?astk0 ?astkb 0) _,
    STK2 : Mem.range_perm ?am ?astkb 0 stack_block_size Cur Writable,
    Hdst_callee :@set_In breg ?dst rbpf_arm_callee_save ,
    Hastk1_eq : @eq (ZMap.t amemval) ?astk1
              (setN (encode_sval_fragments Cany32 (Rval (Sreg (IR (ireg_of_breg ?dst))))) _ ?astk0)
    |- init_arm_stack ?am ?astk1 ?astkb =>
    unfold init_arm_stack;
    split; [| auto];
    rewrite <- STK1;
    unfold astack_load;
    destruct Mem.valid_access_dec; [|reflexivity];
    subst astk1;
    rewrite ab_getN_setN_outside; f_equal;
    simpl;
    left;
    clear - Hdst_callee;
    apply rbpf_arm_callee_save_reg_ge4; auto
  end.

Ltac valid_access_fail_solver := 
  match goal with
  | HF : ~ Mem.valid_access ?am Many32 ?astkb (z_of_breg ?dst * 4) Readable,
    Hrange : Mem.range_perm ?am ?astkb 0 stack_block_size Cur Writable
    |- _ =>
    exfalso; apply HF;
    unfold Mem.valid_access;
    split; [ | unfold align_chunk; simpl; apply Z.divide_factor_r];
    clear - Hrange;
    unfold Mem.range_perm in *;
    intros ofs Hofs;
    eapply Mem.perm_implies; eauto; [ | constructor];
    eapply Hrange; eauto;
    unfold stack_block_size; unfold size_chunk in *;
    clear - Hofs;
    unfold z_of_breg in Hofs; destruct dst; lia
  end.

Lemma aexec_store_ir13:
  forall br (ars: aregset) astk0 astkb am
    (Hdst_callee : In br rbpf_arm_callee_save)
    (REG2 : ars (ireg_of_breg br) = Aval (Rval (Sreg (ireg_of_breg br))))
    (INIT_STK : Mem.range_perm am astkb 0 stack_block_size Cur Writable),
      aexec_store true Many32
          (Some (Aval (Sval Ssp (Ptrofs.of_int (Int.mul (int_of_breg br) (Int.repr 4))))))
          (ireg_of_breg br) ars astk0 astkb am =
        ANext (anextinstr true ars)
          (setN (encode_sval_fragments Cany32 (Rval (Sreg (ireg_of_breg br))))
             (z_of_breg br * 4) astk0)
            astkb am.
Proof.
  intros.
  unfold aexec_store; simpl.
  rewrite ptr_int_mul_4.
  unfold astack_store; simpl.
  destruct Mem.valid_access_dec as [Hvalid | Hno_valid].
  - unfold encode_aval. (**r we need say all initial arm registers have abstract values *)
    rewrite REG2.
    unfold encode_sval; simpl.
    f_equal.
  - exfalso.
    apply Hno_valid.
    clear - INIT_STK.
    unfold Mem.valid_access.
    split.
    + unfold size_chunk, Mem.range_perm in *.
      intros ofs HIn.
      apply INIT_STK.
      unfold stack_block_size.
      destruct br; simpl in HIn; lia.
    + simpl.
      apply Z.divide_factor_r.
Qed.

Lemma set_add_same:
  forall {A:Type} (aeq: forall x y : A, {x = y} + {x <> y}) (l: set A) (x: A),
    (set_add aeq x (set_add aeq x l)) = set_add aeq x l.
Proof.
  induction l; intros.
  - simpl.
    destruct aeq.
    auto.
    exfalso.
    apply n.
    reflexivity.
  - simpl.
    destruct aeq.
    + subst.
      simpl.
      destruct aeq.
      auto.
      exfalso.
      apply n.
      reflexivity.
    + simpl.
      destruct aeq.
      exfalso. apply n. assumption.
      rewrite IHl.
      auto.
Qed.

Ltac in_solver :=
  match goal with
  | |- In ?X ?Y =>
    try (left; reflexivity); right; in_solver
  end.

(*
Lemma rbpf_arm_callee_save_arm_callee_save_iff:
  forall r,
    In r rbpf_arm_callee_save <-> In (ireg_of_breg r) arm_callee_save.
Proof.
  unfold arm_callee_save, rbpf_arm_callee_save.
  unfold ireg_of_breg.
  intros.
  destruct r; split; intro HF;
    repeat (destruct HF as [HF | HF]; [inversion HF | ]); inversion HF;
  in_solver.
Qed. *)


Lemma set_mem_arm_callee_save:
  forall br,
  set_mem breg_eq br rbpf_arm_callee_save = true ->
    In br rbpf_arm_callee_save.
Proof. intros. eapply set_mem_correct1; eauto. (*
  unfold set_mem, arm_callee_save, rbpf_arm_callee_save.
  unfold ireg_of_breg.
  intros.
  destruct ireg_eq as [Heq | Heq]; [| clear Heq].
  { destruct br; inversion Heq.
    simpl; left; reflexivity.
  }
  destruct ireg_eq as [Heq | Heq]; [| clear Heq].
  { destruct br; inversion Heq.
    simpl; do 1 right; left; reflexivity.
  }
  destruct ireg_eq as [Heq | Heq]; [| clear Heq].
  { destruct br; inversion Heq.
    simpl; do 2 right; left; reflexivity.
  }
  destruct ireg_eq as [Heq | Heq]; [| clear Heq].
  { destruct br; inversion Heq.
    simpl; do 3 right; left; reflexivity.
  }
  destruct ireg_eq as [Heq | Heq]; [| clear Heq].
  { destruct br; inversion Heq.
    simpl; do 4 right; left; reflexivity.
  }
  destruct ireg_eq as [Heq | Heq]; [| clear Heq].
  { destruct br; inversion Heq.
    simpl; do 5 right; left; reflexivity.
  }
  destruct ireg_eq as [Heq | Heq]; [| clear Heq].
  { destruct br; inversion Heq.
    simpl; do 6 right; left; reflexivity.
  }
  destruct ireg_eq as [Heq | Heq]; [| clear Heq].
  { destruct br; inversion Heq.
  }
  inversion H. *)
Qed.

Lemma set_mem_arm_callee_save_false:
  forall br,
  set_mem breg_eq br rbpf_arm_callee_save = false ->
    ~In br rbpf_arm_callee_save.
Proof.
  intros. eapply set_mem_complete1; eauto. (*
  intro HF.
  apply set_mem_complete1 in H.
  apply H.
  unfold set_In.
  unfold rbpf_arm_callee_save, arm_callee_save in *.
  clear H; simpl in *.
  do 5 (destruct HF as [HF | HF]; [rewrite <- HF; auto | ]).
  do 4 right; left; reflexivity.
  destruct HF as [HF | HF]; [ rewrite <- HF; do 5 right; left; reflexivity | ].
  destruct HF as [HF | HF]; [ rewrite <- HF; do 6 right; left; reflexivity | ].
  inversion HF. *)
Qed.

Lemma exec_alu32_list_same_mem:
  forall l rs m rs1 m1,
  exec_alu32_list l rs m = Next rs1 m1 ->
    m = m1.
Proof.
  induction l; simpl; intros.
  - inversion H. reflexivity.
  - destruct a; inversion H. clear H1.
    unfold exec_alu32 in H.
    destruct eval_alu32; inversion H. clear H1.
    destruct v; inversion H. clear H1.
    specialize (IHl _ _ _ _ H).
    auto.
Qed.

Lemma exec_alu32_list_change_mem:
  forall l rs m rs1 m1,
  exec_alu32_list l rs m = Next rs1 m ->
    exec_alu32_list l rs m1 = Next rs1 m1.
Proof.
  induction l; simpl; intros.
  - inversion H. reflexivity.
  - destruct a; inversion H. clear H1.
    unfold exec_alu32 in *.
    destruct eval_alu32; inversion H. clear H1.
    destruct v; inversion H. clear H1.
    specialize (IHl _ _ _ m1 H).
    auto.
Qed.


Definition reg_inv (st: state): Prop :=
  match st with
  | State rs _ => forall r, exists vi, rs#r = Vint vi
  end.

Lemma exec_alu32_reg_inv:
  forall op dst src rs0 m0 rs1 m1
  (Hexe_one : exec_alu32 op dst src rs0 m0 = Next rs1 m1)
    (HREG_INV: reg_inv (State rs0 m0)),
      reg_inv (State rs1 m1).
Proof.
  unfold exec_alu32, eval_alu32, reg_inv; intros.
  unfold nextinstr, Val.add, Vone in Hexe_one.

  match goal with
  | H: match ?C with | Some _ => _ | _ => _ end = _ |- _ =>
    destruct C; [| inversion H]
  end.
  destruct v; inversion Hexe_one.

  specialize (HREG_INV BPC) as HPC_eq.
  destruct HPC_eq as (v_pc & HPC_eq).

  destruct (bpreg_eq dst BPC) as [Heq_PC | Hneq_PC] eqn: HPC.
  + rewrite Heq_PC in *.
    erewrite BPregmap.gss; eauto.
    destruct (bpreg_eq r BPC) as [Heq_PC0 | Hneq_PC0] eqn: HPC0.
    * rewrite Heq_PC0 in *.
      erewrite BPregmap.gss; eauto.
    * erewrite ! BPregmap.gso; eauto.
  + destruct (bpreg_eq r BPC) as [Heq_PC0 | Hneq_PC0] eqn: HPC0.
    * rewrite Heq_PC0 in *.
      erewrite BPregmap.gss; eauto.
      erewrite BPregmap.gso; eauto.
      rewrite HPC_eq.
      eauto.
    * erewrite BPregmap.gso; eauto.
      destruct (bpreg_eq r dst) as [Heq_PC1 | Hneq_PC1] eqn: HPC1.
      { rewrite Heq_PC1 in *.
        erewrite BPregmap.gss; eauto.
      }
      { erewrite ! BPregmap.gso; eauto.
      }
Qed.

Lemma exec_alu32_list_reg_inv:
  forall l rs0 m0 rs1 m1
    (HL: exec_alu32_list l rs0 m0 = Next rs1 m1)
    (HREG_INV: reg_inv (State rs0 m0)),
      reg_inv (State rs1 m1).
Proof.
  unfold reg_inv; induction l; simpl; intros.
  - inversion HL; subst.
    apply HREG_INV.
  - destruct a as [| | op dst src | | | | ]; inversion HL.
    destruct exec_alu32 as [rsk mk | ] eqn: Hexe_one; [| inversion HL].
    eapply exec_alu32_reg_inv in Hexe_one.
    2:{ unfold reg_inv; auto. }

    eapply IHl; eauto.
Qed.

Lemma astep_reg_inv:
  forall bpf_get_call mem_map c kl ge m0 t (rs0 rs1: regset) m1
    (HSTEP: astep bpf_get_call mem_map c kl ge (State rs0 m0) t (State rs1 m1))
    (HREG_INV: reg_inv (State rs0 m0)),
      reg_inv (State rs1 m1).
Proof.
  induction 1; unfold reg_inv; intros.
  - eapply exec_alu32_list_reg_inv; eauto.
  - unfold goto_label in H1. (*
    destruct (Pos.to_nat _ <=? _); [| inversion H1]. *)
    injection H1 as Heq Heqm.
    subst m'.
    specialize (HREG_INV r).
    destruct HREG_INV as (vi & HREG_INV).
    rewrite <- Heq.
    destruct (bpreg_eq r BPC) as [Heq_PC | Hneq_PC] eqn: HPC.
    + subst r.
      rewrite H.
      simpl.
      eexists.
      erewrite BPregmap.gss; eauto.
    + exists vi.
      erewrite BPregmap.gso; eauto.
  - unfold exec_branch in H1.
    destruct eval_cmp; [| inversion H1].
    destruct b.
    + unfold goto_label in H1. (*
      destruct (Pos.to_nat _ <=? _); [| inversion H1]. *)
      injection H1 as Heq Heqm.
      subst m'.
      specialize (HREG_INV r0).
      destruct HREG_INV as (vi & HREG_INV).
      rewrite <- Heq.
      destruct (bpreg_eq r0 BPC) as [Heq_PC | Hneq_PC] eqn: HPC.
      * subst r0.
        rewrite H.
        simpl.
        eexists.
        erewrite BPregmap.gss; eauto.
      * exists vi.
        erewrite BPregmap.gso; eauto.
    + injection H1 as Heq Heqm.
      subst m'.
      specialize (HREG_INV r0).
      destruct HREG_INV as (vi & HREG_INV).
      unfold nextinstr, Val.add, Vone in Heq.
      rewrite <- Heq.
      destruct (bpreg_eq r0 BPC) as [Heq_PC | Hneq_PC] eqn: HPC.
      * subst r0.
        erewrite BPregmap.gss; eauto.
        rewrite HREG_INV.
        simpl; eauto.
      * exists vi.
        erewrite BPregmap.gso; eauto.
  - unfold exec_load in H3.
    destruct Mem.loadv as [v_ld |]; [| inversion H3].
    unfold nextinstr, Val.add, Vone in H3.
    destruct v_ld; inversion H3.
    clear H3.
    subst.
    specialize (HREG_INV r0) as Hreg0.
    destruct Hreg0 as (vi0 & Hreg0).
    specialize (HREG_INV r) as Hreg.
    destruct Hreg as (vi & Hreg).

    destruct (bpreg_eq r0 BPC) as [Heq_PC0 | Hneq_PC0] eqn: HPC0.
    + subst r0.
      erewrite BPregmap.gss; eauto.
      destruct (bpreg_eq r BPC) as [Heq_PC | Hneq_PC] eqn: HPC.
      * rewrite Heq_PC in *.
        erewrite BPregmap.gss; eauto.
      * erewrite BPregmap.gso; eauto.
        rewrite Hreg0. eauto.
    + erewrite BPregmap.gso; eauto.
      destruct (bpreg_eq r r0) as [Heq_PC | Hneq_PC] eqn: HPC.
      * rewrite Heq_PC in *.
        erewrite BPregmap.gss; eauto.
      * erewrite BPregmap.gso; eauto.
  - unfold exec_store in H3.
    destruct Mem.storev as [m_st |]; [| inversion H3].
    unfold nextinstr, Val.add, Vone in H3.
    rewrite H in H3.
    injection H3 as Heq Heqm.
    subst.
    specialize (HREG_INV r0) as Hreg0.
    destruct Hreg0 as (vi0 & Hreg0).

    destruct (bpreg_eq r0 BPC) as [Heq_PC | Hneq_PC] eqn: HPC.
    + subst r0.
      erewrite BPregmap.gss; eauto.
    + erewrite BPregmap.gso; eauto.
  - unfold nextinstr, Val.add, Vone in H4.
    erewrite BPregmap.gso in H4.
    2:{ intro HF; inversion HF. }
    rewrite H in H4.
    specialize (HREG_INV r) as Hreg.
    destruct Hreg as (vi & Hreg).
    subst.

    destruct (bpreg_eq r BPC) as [Heq_PC | Hneq_PC] eqn: HPC.
    + subst r.
      erewrite BPregmap.gss; eauto.
    + erewrite BPregmap.gso; eauto.
      destruct (bpreg_eq r R0) as [Heq_PC0 | Hneq_PC0] eqn: HPC0.
      * rewrite Heq_PC0 in *.
        erewrite BPregmap.gss; eauto.
      * erewrite BPregmap.gso; eauto.
Qed.