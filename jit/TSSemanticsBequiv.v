From compcert.lib Require Import Integers Coqlib Maps.
From compcert.common Require Import AST Values Events Globalenvs Memory Memtype.
From compcert.cfrontend Require Import Ctypes.
From compcert.backend Require Import Locations.
From compcert.arm Require Import ABinSem AsmSyntax BinDecode.
From Coq Require Import ZArith Lia List.

From bpf.comm Require Import Flag Regs MemRegion ListAsArray LemmaInt JITCall.
From bpf.rbpf32 Require Import TSSyntax TSDecode Analyzer JITConfig BSemanticsSimpl.
From bpf.jit Require Import TSSemanticsB WholeCompiler TSSemanticsBproofdef TSSemanticsBproof.

Open Scope asm.
Import ListNotations.

Definition memory_region_mapping (mrs: list memory_region) (m: mem) (p: permission) (ck: memory_chunk) (addr: val) (b: block) (ofs: ptrofs): Prop :=
  check_mem p ck addr (List.length mrs) mrs m = Some (Vptr b ofs).

Fixpoint kv_flatten_aux (kv: list (nat * nat)) (l: list nat): option (list nat) :=
  match kv with
  | [] => Some l
  | (k, v) :: tl =>
    match ListNat.assign l k v with
    | None => None
    | Some l' => kv_flatten_aux tl l'
    end
  end.

Definition kv_flatten (kv: list (nat * nat)) (len: nat): option (list nat) :=
  kv_flatten_aux kv (ListNat.create_int_list len).


Axiom kv_flatten_aux_property:
  forall bl kv l v ofs l0 lk sl
  (Hnth : List.In (v, (ofs, l0)) bl)
  (Hconcat : concat_bin bl = (kv, l))
  (HKV: kv_flatten_aux kv lk = Some sl),
    ListNat.index sl v = Some ofs. (*
Proof.
  induction bl; simpl; intros.
  { inversion Hnth. }

  destruct Hnth as [Heq| Hnth].
  { subst a.
    inversion Hconcat; subst. clear Hconcat.
    simpl in HKV.
    (**r we need NoDup info of KV elements *)
  }
Qed. *)

Lemma kv_flatten_property:
  forall bl kv l n v ofs l0 sl len
  (Hnth : nth_error bl n = Some (v, (ofs, l0)))
  (Hconcat : concat_bin bl = (kv, l))
  (HKV: kv_flatten kv len = Some sl),
    ListNat.index sl v = Some ofs.
Proof.
  unfold kv_flatten; intros.
  eapply kv_flatten_aux_property; eauto.
  eapply nth_error_In; eauto.
Qed.


Lemma init_state_pc:
  forall v0 v1 m2  ars1 astk1 astkb1 am
  (Hinit: init_state compcertbin_signature stack_block_size Ptrofs.zero
      [v0; v1] m2 = ANext ars1 astk1 astkb1 am),
    ars1#PC = Cval v0.
Proof.
  unfold init_state, compcertbin_signature, stack_block_size; simpl.
  intros.
  unfold allocframe in Hinit; simpl.
  destruct Mem.alloc as (m0 & stkb) eqn: Halloc.
  unfold init_regset in Hinit.
  unfold astack_store in Hinit.
  change (Ptrofs.unsigned Ptrofs.zero) with 0%Z in Hinit.
  destruct Mem.valid_access_dec as [HL | HR]; [| inversion Hinit].

  unfold encode_aval in Hinit.
  unfold regset0 in Hinit.
  simpl in Hinit.

  injection Hinit as Heq1 Heq2 Heq3 Heq4.
  rewrite <- Heq1; clear.
  rewrite Pregmap.gss.
  rewrite Pregmap.gss.
  reflexivity.
Qed.


Lemma code_subset_in_blk_alloc_unchanged:
forall l ofs jit_blk m x y m1 b,
  code_subset_in_blk l ofs jit_blk m = true ->
  Mem.alloc m x y = (m1, b) ->
  Mem.valid_block m jit_blk ->
    code_subset_in_blk l ofs jit_blk m1 = true /\ Mem.valid_block m1 jit_blk.
Proof.
  induction l; simpl; intros.
  { split; [reflexivity| ].
    eapply Mem.valid_block_alloc; eauto.
  }

  destruct Mem.load as [ins | ] eqn: Hload; [| inversion H].
  eapply Mem.load_alloc_unchanged with (b' := jit_blk) in H0 as Heq; eauto.

  rewrite Heq.
  rewrite Hload.
  destruct ins; inversion H.
  destruct Int.eq; [| inversion H].
  rewrite H.
  eapply IHl; eauto.
Qed.

Lemma code_subset_in_blk_copy_to_unchanged:
  forall l ofs jit_blk m b m1 rs,
    b <> jit_blk ->
    code_subset_in_blk l ofs jit_blk m = true ->
    Mem.valid_block m jit_blk ->
    copy_to rs b m = Some m1 ->
      code_subset_in_blk l ofs jit_blk m1 = true /\ Mem.valid_block m1 jit_blk.
Proof.
  induction l; simpl; intros.
  { split; [reflexivity |].
    unfold copy_to in H2.

    do 11 (
    destruct Mem.store eqn: Hstore; [
      eapply Mem.store_valid_block_1 in Hstore; eauto; clear H1;
      rename Hstore into H1
      | inversion H2]).

    eapply Mem.store_valid_block_1; eauto.
  }

  destruct Mem.load as [ins |] eqn: Hload; [| inversion H0].

  assert (Heq: Mem.load Mint32 m1 jit_blk (Z.of_nat (ofs + (ofs + (ofs + (ofs + 0))))) = Some ins). {
    clear - H Hload H1 H2.
    unfold copy_to in H2.

    do 11 (
    destruct Mem.store eqn: Hstore; [
      eapply Mem.load_store_other in Hstore; eauto;
      rewrite <- Hstore in Hload; clear Hstore
      | inversion H2]).

    eapply Mem.load_store_other in H2; eauto.
    rewrite H2; auto.
  }

  rewrite Heq; clear Heq.
  destruct ins; inversion H0.
  destruct Int.eq; [| inversion H0].
  rewrite H0.
  eapply IHl; eauto.
Qed.

Lemma code_subset_in_blk_init_state_unchanged:
forall l ofs jit_blk m v0 v1 ars1 astk1 astkb1 m1,
  code_subset_in_blk l ofs jit_blk m = true ->
  Mem.valid_block m jit_blk ->
  init_state compcertbin_signature stack_block_size Ptrofs.zero
      [v0; v1] m = ANext ars1 astk1 astkb1 m1 ->
    code_subset_in_blk l ofs jit_blk m1 = true.
Proof.
  unfold init_state, compcertbin_signature, stack_block_size; simpl.
  intros.
  rename H1 into Hinit.
  unfold allocframe in Hinit; simpl.
  destruct Mem.alloc as (m0 & stkb) eqn: Halloc.
  unfold init_regset in Hinit.
  unfold astack_store in Hinit.
  change (Ptrofs.unsigned Ptrofs.zero) with 0%Z in Hinit.
  destruct Mem.valid_access_dec as [HL | HR]; [| inversion Hinit].

  unfold encode_aval in Hinit.
  unfold regset0 in Hinit.
  simpl in Hinit.

  injection Hinit as Heq1 Heq2 Heq3 Heq4.
  rewrite <- Heq4; clear - H H0 Halloc.
  eapply code_subset_in_blk_alloc_unchanged; eauto.
Qed.

Lemma jit_len_max:
  forall c kl bl kv l l0 v ofs n
  (Hjit_len_max : List.length l < JITTED_LIST_MAX_LENGTH)
  (Hnth : nth_error bl n = Some (v, (ofs, l0)))
  (Hanalyzer : analyzer c = Some kl)
  (Hcombiner : combiner kl = Some bl)
  (Hconcat : concat_bin bl = (kv, l)),
    List.length l0 < JITTED_LIST_MAX_LENGTH /\
    ((Z.of_nat (ofs + Datatypes.length l0) * 4) < Int.max_unsigned)%Z.
Proof.
  intros.
  eapply nth_error_combiner in Hcombiner as Heq; eauto.
  destruct Heq as (l1 & Hcom).
  eapply combiner_nth_error in Hcom; eauto.
  destruct Hcom as (ofs1 & bl1 & Hnth1 & Hcomp & Halu32 & HMAX & HMAX1).
  rewrite Hnth in Hnth1.
  inversion Hnth1; subst.
  split; auto.
Qed.

Fixpoint exec_bin_list_inv (l: bin_code) (ofs: nat) (jit_blk: block)
  (ars: aregset) (astk: astack) (astkb: block) (m: mem): Prop :=
  if is_final_state ars then
    True
  else
    match l with
    | [] => True
    | hd :: tl =>
      (code_subset_in_blk l ofs jit_blk m = true) /\
      (ars#PC = Cval (Vptr jit_blk (Ptrofs.of_int (Int.repr (Z.of_nat (4* ofs)))))) /\
      match decode_thumb hd with
      | None => False
      | Some arm_ins =>
        match aexec_instr true arm_ins ars astk astkb m with
        | AStuck => False
        | ANext ars' astk' astkb' m' =>
          (code_subset_in_blk tl (ofs+1) jit_blk m' = true) /\
          (astkb = astkb') /\
          (exec_bin_list_inv tl (ofs+1) jit_blk ars' astk' astkb' m')
        end
      end
  end.

Axiom jit_inv1: forall l n v c kl kv bl ls ofs jit_blk ars1 stk1 stkb1 m1 ars2 stk2 stkb2 m2
  (Hnth : nth_error bl n = Some (v, (ofs, l)))
  (Hanalyzer : analyzer c = Some kl)
  (Hcombiner : combiner kl = Some bl)
  (Hconcat : concat_bin bl = (kv, ls)),
    code_subset_in_blk l ofs jit_blk m1 = true ->
    exec_bin_list l ars1 stk1 stkb1 m1 = ANext ars2 stk2 stkb2 m2 ->
    exec_bin_list_inv l ofs jit_blk ars1 stk1 stkb1 m1.

Lemma bin_interp_less_fuel:
  forall n rt k ars2 stk2 stkb2 m1 res m2,
  bin_interp rt n ars2 stk2 stkb2 m1 = Some (res, m2) ->
  n <= k ->
  bin_interp rt k ars2 stk2 stkb2 m1 = Some (res, m2).
Proof.
  induction n; intros.
  { simpl in H.
    destruct k.
    - simpl.
      auto.
    - simpl.
      destruct is_final_state; [| inversion H].
      auto.
  }

  simpl in H.
  destruct is_final_state eqn: Hfinal.
  {
    (**r is final *)
    destruct k.
    - inversion H0.
    - simpl.
      rewrite Hfinal.
      auto.
  }

  (**r is NOT final *)
  destruct ABinSem.find_instr as [ (i & sz) | ] eqn: Hfind;
  [| inversion H].
  destruct aexec_instr as [ rs' stk' stkb m' | ] eqn: Hexe;
  [| inversion H].
  destruct k; [inversion H0 |].
  assert (Heq: n <= k) by lia.
  simpl.
  rewrite Hfinal.
  rewrite Hfind.
  rewrite Hexe.
  eapply IHn; eauto.
Qed.

Lemma exec_bin_list_bin_interp:
  forall l ofs jit_blk ars1 stk1 stkb1 m1 ars2 stk2 k stkb2 m2
  (Hsubst : exec_bin_list_inv l ofs jit_blk ars1 stk1 stkb1 m1)
  (Hofs: (Z.of_nat ((ofs + List.length l) * 4) < Int.max_unsigned)%Z)
  (Hlen: List.length l < k)
  (Hexec: exec_bin_list l ars1 stk1 stkb1 m1 = ANext ars2 stk2 stkb2 m2)
  (Hfinal: is_final_state ars2 = true)
  (Hars_r0 : get_result_bool AST.Tint (ars2#IR0) = true) (*
  (Hars_pc : ars1#PC =
          Cval
            (Vptr jit_blk
               (Ptrofs.of_int (Int.repr (Z.of_nat ofs))) )) *),
    exists res,
    bin_interp (sig_res compcertbin_signature)
        k ars1 stk1 stkb1 m1 = Some (res, m2).
Proof.
  induction l; intros.
  {
    simpl in Hexec.
    destruct is_final_state eqn: His_final;
    injection Hexec as Hrs_eq Hstk_eq; subst.
    - unfold get_result_bool in Hars_r0.
      destruct (ars2 IR0) as [ v_r0 | ] eqn: Heq; [| inversion Hars_r0].
      exists v_r0.
      erewrite bin_interp_less_fuel with (n := 0); eauto.
      2:{ lia. }
      simpl.
      rewrite Hfinal.
      unfold get_result; simpl.
      simpl in Hars_r0.
      rewrite Heq.
      rewrite Hars_r0.
      reflexivity.
    - exfalso.
      rewrite His_final in Hfinal.
      inversion Hfinal.
  }

  destruct k.
  { (**r k = 0 *)
    inversion Hlen.
  }

  simpl in Hexec.
  simpl.
  destruct is_final_state eqn: His_final.
  { inversion Hexec; subst.
    unfold get_result_bool in Hars_r0.
    unfold get_result.
    destruct (ars2 IR0) as [v_r0 | ] eqn: Hars_r0_eq; [| inversion Hars_r0].
    rewrite Hars_r0.
    eexists; f_equal.
  }

  unfold ABinSem.find_instr.
  simpl in Hsubst.
  rewrite His_final in Hsubst.
  destruct Hsubst as (Hmem1 & Hpc & Hsubst).

  destruct Mem.load as [ins | ] eqn: Hload; [| inversion Hmem1].
  destruct ins; inversion Hmem1; subst.
  clear H0.
  destruct Int.eq eqn: Heq; [| inversion Hmem1].
  apply Int.same_if_eq in Heq.
  subst i.

  rewrite Hpc.
  unfold BinDecode.find_instr.
  unfold Ptrofs.of_int.
  unfold Mem.loadv.
  rewrite Int.unsigned_repr.
  2:{ lia. }
  rewrite Ptrofs.unsigned_repr.
  2:{ change Ptrofs.max_unsigned with Int.max_unsigned; lia. }

  rewrite Hload.

  destruct decode_thumb as [arm_ins | ] eqn: Hdecode; [| inversion Hexec].
  simpl.

  destruct aexec_instr as [ars' astk' astkb' m' | ] eqn: Hinstr; [| inversion Hexec].
  destruct Hsubst as (Hsubst1 & Hstkb_eq & Hsubst).

  simpl in IHl.
  eapply IHl with (ofs := ofs+1) (jit_blk := jit_blk); eauto.
  - clear - Hofs.
    simpl in Hofs.
    lia.
  - clear - Hlen.
    simpl in Hlen.
    lia.
Qed.


Section Forward4.

Hypothesis _bpf_get_call: ident -> genv -> option fundef.

Axiom _bpf_get_call_equiv:
  forall s ge ef (rs rs': regset) m t res args m' sg
  (Hcall : _bpf_get_call s ge = Some (AST.External ef))
  (Hargs : args = [rs R1; rs R2; rs R3; rs R4; rs R5])
  (Hext : external_call ef ge args m t (Vint res) m')
  (Hrs1 : rs' = nextinstr (BPregmap.set R0 (Vint res) rs)),
  BState._bpf_get_call s sg m = Some (Vint res, m').

Lemma jit_call_simpl_exec_bin_code_equiv:
  forall bl n v l0 ofs jit_blk m (rs rs': regset) m' c kl kv l sl
  (Hvalid_jit : Mem.valid_block m jit_blk)
  (Hnth : nth_error bl n = Some (v, (ofs, l0)))
  (Hofs: (Z.of_nat ((ofs + List.length l0) * 4) < Int.max_unsigned)%Z)
  (Hsubst : code_subset_in_blk l0 ofs jit_blk m = true)
  (Hexe : exec_bin_code l0 ofs jit_blk rs m = Next rs' m')
  (Hpc_eq : Vint (Int.repr (Z.of_nat v)) = rs BPC)
  (Hjit_blk : jit_arm_block = jit_blk)
  (Hlen_max : Datatypes.length c <= 5000)
  (Hlen: List.length l0 < JITTED_LIST_MAX_LENGTH)
  (Hanalyzer : analyzer c = Some kl)
  (Hcombiner : combiner kl = Some bl)
  (Hconcat : concat_bin bl = (kv, l))
  (Hreg_inv: reg_inv (State rs m))
  (Hle_pc : v < Datatypes.length c)
  (HKV: kv_flatten kv (Datatypes.length c) = Some sl),
    match BState.jit_call_simplb sl rs m with
    | Some (rs'0, m'0) => Some (rs'0, m'0, BPF_OK)
    | None => None
    end = Some (rs', m', BPF_OK).
Proof.

  intros.
  unfold BState.jit_call_simplb.
  rewrite Hjit_blk; clear Hjit_blk.

  rewrite <- Hpc_eq.
  assert (Heq: Z.to_nat (Int.unsigned (Int.repr (Z.of_nat v))) = v). {
    rewrite Int.unsigned_repr.
    apply Nat2Z.id.
    change Int.max_unsigned with 4294967295%Z; lia.
  }
  rewrite Heq; clear Heq.
  erewrite kv_flatten_property; eauto.

  unfold exec_bin_code in Hexe.
  unfold state_block_size, stack_block_size in *.
  destruct Mem.alloc eqn: Halloc.
  destruct copy_to as [m1 | ] eqn: Hcopy_to; [| inversion Hexe].

  unfold bin_exec.
  change (Int.unsigned (Int.repr 48%Z)) with 48%Z.
  assert (Heq: Val.add (Vptr jit_blk Ptrofs.zero) (Vint (Int.repr (Z.of_nat (4 * ofs)))) = 
    Vptr jit_blk (Ptrofs.of_intu (Int.repr (Z.of_nat (4 * ofs))))). {
    clear.
    simpl.
    f_equal.
    rewrite Ptrofs.add_zero_l.
    unfold Ptrofs.of_intu.
    f_equal.
  }
  rewrite Heq in Hexe; clear Heq.
  destruct init_state as [ars1 stk1 stkb1 am | ]
    eqn: Hinit_state; [| inversion Hexe].

  simpl in Hinit_state.

  assert (Hars_pc: ars1#PC = Cval (Vptr jit_blk
                   (Ptrofs.of_int (Int.repr
                            (Z.of_nat (ofs + (ofs + (ofs + (ofs + 0))))))
(*
                      (Int.mul
                         (Int.repr
                            (Z.of_nat ofs))
                         (Int.repr 2)) *) ))). {
    eapply init_state_pc; eauto.
  } (*
  destruct Hars_pc as (Hars_r0 & Hars_pc). *)

  destruct exec_bin_list as [ars2 astk2 astkb2 am2 | ] eqn: Hexec; [| inversion Hexe].
  destruct is_final_state eqn: Hfinal; [| inversion Hexe].

  eapply code_subset_in_blk_alloc_unchanged in Hsubst; eauto.
  destruct Hsubst as (Hsubst & Hvalid_m0).

  assert (Hblk_neq: b <> jit_blk). {
    intro HF.
    eapply Mem.fresh_block_alloc; eauto.
    subst b.
    auto.
  }

  eapply code_subset_in_blk_copy_to_unchanged in Hsubst; eauto.
  destruct Hsubst as (Hsubst & Hvalid_m1).
  eapply code_subset_in_blk_init_state_unchanged in Hsubst; eauto.


  destruct get_result_bool eqn: Hget_result; [| inversion Hexe].
  eapply jit_inv1 in Hsubst; eauto.

  eapply exec_bin_list_bin_interp in Hsubst; eauto.

  destruct Hsubst as (res & Hinterp).
  rewrite Hinterp.

  destruct copy_from as [rs1 | ] eqn: Hcopy_from; [| inversion Hexe].
  injection Hexe as Hrs1_eq Hm_eq; subst rs' m'.
  reflexivity.
Qed.


Theorem forward_from_ts_to_interpreter_simpl:
  forall rs1 rs2 st1 st2 m1 m2 c kl bl kv l ge jit_blk t mrs sl,
    bstep _bpf_get_call (memory_region_mapping mrs) c bl jit_blk ge
      st1 t st2 ->

    st1 = State rs1 m1 ->
    st2 = State rs2 m2 ->

    jit_arm_block = jit_blk ->
    Mem.valid_block m1 jit_blk ->

    List.length c <= MAX_BPF_LIST_INPUT ->
    analyzer c = Some kl ->
    combiner kl = Some bl ->
    concat_bin bl = (kv, l) ->
    reg_inv st1 ->
    List.length l < JITTED_LIST_MAX_LENGTH ->
    kv_flatten kv (List.length c) = Some sl ->

    step c sl (List.length c) rs1 (List.length mrs) mrs m1 =
      Some (rs2, m2, BPF_OK).
Proof.
  induction 1; intros Hst1 Hst2 Hjit_blk Hvalid_jit Hlen_max Hanalyzer
    Hcombiner Hconcat Hreg_inv Hjit_len_max HKV;
    injection Hst1 as Heq1 Heq2; subst rs1 m1;
    injection Hst2 as Heq3 Heq4; subst rs2 m2;
    unfold step, eval_ins.
  - rename H into HPC.
    rename H0 into Hfind.
    rename H1 into Hnth.
    rename H2 into Hsubst.
    rename H3 into Hexe.

    eapply jit_len_max in Hjit_len_max; eauto.
    destruct Hjit_len_max as (Hjit_len_max1 & Hjit_len_max2).

    unfold find_instr in Hfind.
    destruct nth_error eqn: Hnth_pc; [| inversion Hfind].
    rewrite HPC.

    unfold MAX_BPF_LIST_INPUT in Hlen_max.

    (**r pc1 <= List.length c because of find_instr = Some *)
    assert (Hle_pc: v < List.length c). {
      apply nth_error_Some.
      intro HF.
      rewrite HF in Hnth_pc.
      inversion Hnth_pc.
    }

    assert (Heq: Int.cmpu Clt (Int.repr (Z.of_nat v))
      (Int.repr (Z.of_nat (Datatypes.length c))) = true). {
      clear - Hlen_max Hnth_pc Hle_pc.
      simpl.
      rewrite Clt_Zlt_unsigned.
      do 2 (rewrite Int.unsigned_repr; [|
        change Int.max_unsigned with 4294967295%Z; lia ]).
      lia.
    }
    rewrite Heq; clear Heq.
    rewrite Int.unsigned_repr; [|
      change Int.max_unsigned with 4294967295%Z; lia ].
    rewrite Nat2Z.id.
    rewrite Hnth_pc.

    rewrite Hfind.
    eapply jit_call_simpl_exec_bin_code_equiv; eauto. lia.
  - (**r JMP_always *)
    rename H into HPC.
    rename H0 into Hfind.
    rename H1 into Hexe.

    unfold find_instr in Hfind.
    destruct nth_error eqn: Hnth_pc; [| inversion Hfind].
    rewrite HPC.

    unfold MAX_BPF_LIST_INPUT in Hlen_max.

    (**r pc1 <= List.length c because of find_instr = Some *)
    assert (Hle_pc: v < List.length c). {
      apply nth_error_Some.
      intro HF.
      rewrite HF in Hnth_pc.
      inversion Hnth_pc.
    }

    assert (Heq: Int.cmpu Clt (Int.repr (Z.of_nat v))
      (Int.repr (Z.of_nat (Datatypes.length c))) = true). {
      clear - Hlen_max Hnth_pc Hle_pc.
      simpl.
      rewrite Clt_Zlt_unsigned.
      do 2 (rewrite Int.unsigned_repr; [|
        change Int.max_unsigned with 4294967295%Z; lia ]).
      lia.
    }
    rewrite Heq; clear Heq.
    rewrite Int.unsigned_repr; [|
      change Int.max_unsigned with 4294967295%Z; lia ].
    rewrite Nat2Z.id.
    rewrite Hnth_pc.

    rewrite Hfind.
    unfold goto_label in Hexe.
    injection Hexe as Heq1 Heq2; subst.
    rewrite <- HPC.
    reflexivity.

  - (**r JMP Cond *)
    rename H into HPC.
    rename H0 into Hfind.
    rename H1 into Hexe.

    unfold goto_label in Hexe.

    unfold find_instr in Hfind.
    destruct nth_error eqn: Hnth_pc; [| inversion Hfind].
    rewrite HPC.

    unfold MAX_BPF_LIST_INPUT in Hlen_max.

    (**r pc1 <= List.length c because of find_instr = Some *)
    assert (Hle_pc: v < List.length c). {
      apply nth_error_Some.
      intro HF.
      rewrite HF in Hnth_pc.
      inversion Hnth_pc.
    }

    assert (Heq: Int.cmpu Clt (Int.repr (Z.of_nat v))
      (Int.repr (Z.of_nat (Datatypes.length c))) = true). {
      clear - Hlen_max Hnth_pc Hle_pc.
      simpl.
      rewrite Clt_Zlt_unsigned.
      do 2 (rewrite Int.unsigned_repr; [|
        change Int.max_unsigned with 4294967295%Z; lia ]).
      lia.
    }
    rewrite Heq; clear Heq.
    rewrite Int.unsigned_repr; [|
      change Int.max_unsigned with 4294967295%Z; lia ].
    rewrite Nat2Z.id.
    rewrite Hnth_pc.

    rewrite Hfind.
    unfold exec_branch in Hexe.
    destruct eval_cmp as [b|] eqn: Hcmp; [| inversion Hexe].
    destruct b.
    + unfold goto_label in Hexe.
      injection Hexe as Heq1 Heq2; subst.
      rewrite <- HPC.
      reflexivity.
    + injection Hexe as Heq1 Heq2; subst.
      reflexivity.

  - (**r Load *)
    rename H into HPC.
    rename H0 into Hfind.
    rename H1 into Hregion.
    rename H2 into Hexe.

    rewrite HPC.
    unfold find_instr in Hfind.
    destruct nth_error eqn: Hnth_pc; [| inversion Hfind].

    unfold MAX_BPF_LIST_INPUT in Hlen_max.

    (**r pc1 <= List.length c because of find_instr = Some *)
    assert (Hle_pc: v < List.length c). {
      apply nth_error_Some.
      intro HF.
      rewrite HF in Hnth_pc.
      inversion Hnth_pc.
    }

    assert (Heq: Int.cmpu Clt (Int.repr (Z.of_nat v))
      (Int.repr (Z.of_nat (Datatypes.length c))) = true). {
      clear - Hlen_max Hnth_pc Hle_pc.
      simpl.
      rewrite Clt_Zlt_unsigned.
      do 2 (rewrite Int.unsigned_repr; [|
        change Int.max_unsigned with 4294967295%Z; lia ]).
      lia.
    }
    rewrite Heq; clear Heq.
    rewrite Int.unsigned_repr; [|
      change Int.max_unsigned with 4294967295%Z; lia ].
    rewrite Nat2Z.id.
    rewrite Hnth_pc.

    rewrite Hfind.
    unfold memory_region_mapping in Hregion.
    unfold step_load_x_operation.
    unfold rBPFValues.sint32_to_vint.
    rewrite Hregion.
    unfold rBPFValues.cmp_ptr32_null.

    eapply check_mem_prop in Hregion; eauto.
    destruct Hregion as [(b0 & ofs0 &Heq & Hvalid1 & Hvalid2)| HF].
    2:{ inversion HF. }
    injection Heq as Heq1 Heq2; subst b0 ofs0.
    simpl.
    rewrite Hvalid1.
    rewrite Int.eq_true.
    simpl.
    unfold exec_load in Hexe.
    unfold load_mem.
    destruct Mem.loadv eqn: Hload.
    + destruct k; simpl; simpl in Hexe;
      destruct v0; inversion Hexe; clear H0; f_equal.
    + inversion Hexe.

  - (**r Store *)
    rename H into HPC.
    rename H0 into Hfind.
    rename H1 into Hregion.
    rename H2 into Hexe.

    rewrite HPC.
    unfold find_instr in Hfind.
    destruct nth_error eqn: Hnth_pc; [| inversion Hfind].

    unfold MAX_BPF_LIST_INPUT in Hlen_max.

    (**r pc1 <= List.length c because of find_instr = Some *)
    assert (Hle_pc: v < List.length c). {
      apply nth_error_Some.
      intro HF.
      rewrite HF in Hnth_pc.
      inversion Hnth_pc.
    }

    assert (Heq: Int.cmpu Clt (Int.repr (Z.of_nat v))
      (Int.repr (Z.of_nat (Datatypes.length c))) = true). {
      clear - Hlen_max Hnth_pc Hle_pc.
      simpl.
      rewrite Clt_Zlt_unsigned.
      do 2 (rewrite Int.unsigned_repr; [|
        change Int.max_unsigned with 4294967295%Z; lia ]).
      lia.
    }
    rewrite Heq; clear Heq.
    rewrite Int.unsigned_repr; [|
      change Int.max_unsigned with 4294967295%Z; lia ].
    rewrite Nat2Z.id.
    rewrite Hnth_pc.

    rewrite Hfind.
    unfold memory_region_mapping in Hregion.
    unfold step_store_operation.
    unfold rBPFValues.sint32_to_vint.
    rewrite Hregion.
    unfold rBPFValues.cmp_ptr32_null.

    eapply check_mem_prop in Hregion; eauto.
    destruct Hregion as [(b0 & ofs0 &Heq & Hvalid1 & Hvalid2)| HF].
    2:{ inversion HF. }
    injection Heq as Heq1 Heq2; subst b0 ofs0.
    simpl.
    rewrite Hvalid1.
    rewrite Int.eq_true.
    simpl.
    unfold exec_store in Hexe.
    unfold store_mem.
    destruct ri as [src_r | src_i].
    + destruct Mem.storev eqn: Hload.
      * destruct k; simpl; simpl in Hexe;
        inversion Hexe; clear H0; f_equal.
      * inversion Hexe.
    + destruct Mem.storev eqn: Hload.
      * destruct k; simpl; simpl in Hexe;
        inversion Hexe; clear H0; f_equal.
      * inversion Hexe.

  - (**r Call *)
    rename H into HPC.
    rename H0 into Hfind.
    rename H1 into Hcall.
    rename H2 into Hargs.
    rename H3 into Hext.
    rename H4 into Hrs1.

    rewrite HPC.
    unfold find_instr in Hfind.
    destruct nth_error eqn: Hnth_pc; [| inversion Hfind].

    unfold MAX_BPF_LIST_INPUT in Hlen_max.

    (**r pc1 <= List.length c because of find_instr = Some *)
    assert (Hle_pc: v < List.length c). {
      apply nth_error_Some.
      intro HF.
      rewrite HF in Hnth_pc.
      inversion Hnth_pc.
    }

    assert (Heq: Int.cmpu Clt (Int.repr (Z.of_nat v))
      (Int.repr (Z.of_nat (Datatypes.length c))) = true). {
      clear - Hlen_max Hnth_pc Hle_pc.
      simpl.
      rewrite Clt_Zlt_unsigned.
      do 2 (rewrite Int.unsigned_repr; [|
        change Int.max_unsigned with 4294967295%Z; lia ]).
      lia.
    }
    rewrite Heq; clear Heq.
    rewrite Int.unsigned_repr; [|
      change Int.max_unsigned with 4294967295%Z; lia ].
    rewrite Nat2Z.id.
    rewrite Hnth_pc.

    rewrite Hfind.
    erewrite _bpf_get_call_equiv; eauto.
    subst rs'.
    reflexivity.
Qed.
End Forward4.