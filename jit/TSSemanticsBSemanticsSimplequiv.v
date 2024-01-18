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

(*
Fixpoint memory_region_mapping (mrs: list memory_region) (addr: val) (b: block) (ofs: ptrofs): Prop :=
  match mrs with
  | [] => False
  | hd :: tl =>
    if Val.eq (start_addr hd) vb then
      if Val.eq (block_ptr hd) (Vptr b Ptrofs.zero) then
        True
      else
        memory_region_mapping tl b vb
    else
      memory_region_mapping tl b vb
  end. *)
(*
Definition match_state (st: state) (brs: regset) (bm: mem) (f: bpf_flag): Prop :=
  match st with
  | State rs m =>
    brs = rs /\
    bm = m /\
    f = BPF_OK
  end. *)

Fixpoint kv_flatten_aux (kv: list (nat * nat)) (l: list nat): list nat :=
  match kv with
  | [] => l
  | (k, v) :: tl =>
    match ListNat.assign l k v with
    | None => []
    | Some l' => kv_flatten_aux tl l'
    end
  end.

Definition kv_flatten (kv: list (nat * nat)) (len: nat): list nat :=
  kv_flatten_aux kv (ListNat.create_int_list len).



Lemma kv_flatten_property:
  forall c kl bl kv l v_pc ofs jit_blk m1
  (Hkv_ofs : ListNat.index (kv_flatten kv (Datatypes.length c)) (Z.to_nat (Int.unsigned v_pc)) =
          Some ofs)
  (Hsubst : code_subset_in_blk l 0 jit_blk m1 = true)
  (Hlen_max : Datatypes.length c <= MAX_BPF_LIST_INPUT)
  (Hanalyzer : analyzer c = Some kl)
  (Hcombiner : combiner kl = Some bl)
  (Hconcat : concat_bin bl = (kv, l)),
    exists nl : bin_code,
      List.In (Z.to_nat (Int.unsigned v_pc), (ofs, nl)) bl /\
      code_subset_in_blk nl ofs jit_blk m1 = true.
Proof.
  (**r this is a property of kv_flatten, do it later *)
Admitted.

Lemma init_state_pc:
  forall v0 v1 m2  ars1 astk1 astkb1 am
  (Hinit: init_state compcertbin_signature stack_block_size Ptrofs.zero
      [v0; v1] m2 = ANext ars1 astk1 astkb1 am),
    ars1#PC = Cval v0.
Proof.
  (**r unfold init_state imply the result *)
Admitted.


Lemma code_subset_in_blk_alloc_unchanged:
forall l ofs jit_blk m x y m1 b,
  code_subset_in_blk l ofs jit_blk m = true ->
  Mem.alloc m x y = (m1, b) ->
    code_subset_in_blk l ofs jit_blk m1 = true.
Proof.

Admitted.

Lemma code_subset_in_blk_copy_to_unchanged:
forall l ofs jit_blk m b m1 rs,
  code_subset_in_blk l ofs jit_blk m = true ->
  copy_to rs b m = Some m1 ->
    code_subset_in_blk l ofs jit_blk m1 = true.
Proof.

Admitted.

Lemma code_subset_in_blk_init_state_unchanged:
forall l ofs jit_blk m v0 v1 ars1 astk1 astkb1 m1,
  code_subset_in_blk l ofs jit_blk m = true ->
  init_state compcertbin_signature stack_block_size Ptrofs.zero
      [v0; v1] m = ANext ars1 astk1 astkb1 m1 ->
    code_subset_in_blk l ofs jit_blk m1 = true.
Proof.

Admitted.

(*
Lemma copy_from_reg_inv:
  forall rs b am2 rs1 v m brs1
  (Hcopy_from : copy_from rs b am2 =
               Some rs1)
  (Hpc_eq : Vint (Int.repr (Z.of_nat v)) =
           rs BPC)
  (Hreg_eq : forall r : reg,
            exists vi : val,
              eval_regmap r brs1 = vi /\
              vi = rs (reg_to_breg r))
  (Hreg_inv : reg_inv (State rs m)),
    reg_inv (State rs1 m).
Proof.

Admitted. *)

(*
Lemma jit_len_max:
  forall c kl bl kv l l0 v ofs n
  (Hjit_len_max : List.length l < JITTED_LIST_MAX_LENGTH)
  (Hnth : nth_error bl n = Some (v, (ofs, l0)))
  (Hanalyzer : analyzer c = Some kl)
  (Hcombiner : combiner kl = Some bl)
  (Hconcat : concat_bin bl = (kv, l)),
    List.length l0 < JITTED_LIST_MAX_LENGTH /\
    (Z.of_nat (ofs + Datatypes.length l0 * 4) < Int.max_unsigned)%Z.
Proof.

Admitted.

Fixpoint exec_bin_list_inv (l: bin_code) (ofs: nat) (jit_blk: block)
  (ars: aregset) (astk: astack) (astkb: block) (m: mem): Prop :=
  if is_final_state ars then
    True
  else
    match l with
    | [] => True
    | hd :: tl =>
      (code_subset_in_blk l ofs jit_blk m = true) /\
      (ars#PC = Cval (Vptr jit_blk (Ptrofs.of_int (Int.repr (Z.of_nat ofs))))) /\
      match decode_thumb hd with
      | None => False
      | Some arm_ins =>
        match aexec_instr true arm_ins ars astk astkb m with
        | AStuck => False
        | ANext ars' astk' astkb' m' =>
          (code_subset_in_blk tl (ofs+4) jit_blk m' = true) /\
          (astkb = astkb') /\
          (exec_bin_list_inv tl (ofs+4) jit_blk ars' astk' astkb' m')
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
    exec_bin_list_inv l ofs jit_blk ars1 stk1 stkb1 m1. *)

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

(*
Lemma exec_bin_list_bin_interp:
  forall l ofs jit_blk ars1 stk1 stkb1 m1 ars2 stk2 k stkb2 m2
  (Hsubst : exec_bin_list_inv l ofs jit_blk ars1 stk1 stkb1 m1)
  (Hofs: (Z.of_nat (ofs + (List.length l) * 4) < Int.max_unsigned)%Z)
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
  eapply IHl with (ofs := ofs+4) (jit_blk := jit_blk); eauto.
  - clear - Hofs.
    simpl in Hofs.
    lia.
  - clear - Hlen.
    simpl in Hlen.
    lia.
Qed. *)


(**r the lemma has been proven in CertrBPF: /CAV22-AE/isolation/CheckMem.v
  mem_inv_check_mem_valid_pointer
  Here we skip the proof.
*)
Axiom check_mem_prop:
  forall p ck addr n mrs m ptr,
  check_mem p ck addr n mrs m = Some ptr ->
    (exists b ofs, ptr = Vptr b ofs /\
        (Mem.valid_pointer m b (Ptrofs.unsigned ofs)
          || Mem.valid_pointer m b (Ptrofs.unsigned ofs - 1) = true)%bool /\
        Mem.valid_block m b)
        \/ ptr = Vnullptr.


Axiom aexec_instr_inv:
  forall sz i (rs0 rs1: aregset) stk stkb m0 stk1 stkb1 m1 jit_blk ofs,
    rs0#PC = Cval (Vptr jit_blk (Ptrofs.of_int (Int.repr (Z.of_nat ofs)))) ->
    aexec_instr sz i rs0 stk stkb m0 = ANext rs1 stk1 stkb1 m1 ->
      rs1#PC = Cval (Vptr jit_blk (Ptrofs.of_int (Int.repr (Z.of_nat (ofs + 4))))) /\
      ((Z.of_nat ofs+4) <= Ptrofs.max_unsigned)%Z /\
      Mem.unchanged_on (fun (b : block) (_ : Z) => b = jit_blk) m0 m1.

Lemma code_subset_in_blk_unchange:
  forall nl ofs jit_blk m5 m'
  (Hsubst : code_subset_in_blk nl ofs jit_blk m5 = true)
  (Hunchanged : Mem.unchanged_on (fun (b : block) (_ : Z) => b = jit_blk) m5 m'),
    code_subset_in_blk nl ofs jit_blk m' = true.
Proof.
  induction nl; simpl; intros.
  { reflexivity. }

  destruct Mem.load eqn: Hload in Hsubst; [| inversion Hsubst].
  destruct v; inversion Hsubst; clear H0.
  rewrite Hsubst.
  eapply Mem.load_unchanged_on_1 with (chunk := Mint32) (ofs := (Z.of_nat ofs)) in Hunchanged as Heq; eauto.
  2:{ eapply Mem.load_valid_access in Hload; eauto.
    eapply Mem.valid_access_valid_block with (chunk := Mint32) (ofs := (Z.of_nat ofs)); eauto.
    eapply Mem.valid_access_implies; eauto.
    constructor.
  }

  rewrite Heq.
  rewrite Hload.
  destruct Int.eq; [| inversion Hsubst].
  eapply IHnl; eauto.
Qed.

Lemma bin_interp_exec_bin_list:
  forall nl ofs jit_blk m5 rs stk stkb res m6
  (Hsubst: code_subset_in_blk nl ofs jit_blk m5 = true)
  (Hpc: rs#PC = Cval (Vptr jit_blk (Ptrofs.of_int (Int.repr (Z.of_nat ofs)))))
  (Hinterp: bin_interp (sig_res compcertbin_signature) (List.length nl) rs stk stkb m5 = Some (res, m6)),
  exists rs1 stk1 stkb1,
    exec_bin_list nl rs stk stkb m5 = ANext rs1 stk1 stkb1 m6 /\
    is_final_state rs1 = true /\
    get_result_bool AST.Tint (rs1 IR0) = true.
Proof.
  induction nl; simpl; intros.
  { exists rs, stk, stkb.
    destruct is_final_state eqn: Hfinal.
    - unfold get_result in Hinterp.
      unfold get_result_bool.
      destruct (rs IR0).
      + destruct (_ && _).
        * inversion Hinterp; auto.
        * inversion Hinterp.
      + inversion Hinterp.
    - inversion Hinterp.
  }

  destruct Mem.load as [ins | ] eqn: Hload_ins; [| inversion Hsubst].
  destruct ins; inversion Hsubst; clear H0.
  rewrite Hsubst.
  unfold ABinSem.find_instr in Hinterp.
  unfold BinDecode.find_instr in Hinterp.
  destruct is_final_state eqn: Hfinal.
  { unfold get_result in Hinterp.
    unfold get_result_bool.
    exists rs, stk, stkb.
    destruct (rs IR0); [| inversion Hinterp].
    destruct (_ && _); [| inversion Hinterp].
    inversion Hinterp; auto.
  }

  rewrite Hpc in Hinterp.
  simpl in Hinterp.
  destruct Mem.load eqn: Hload in Hinterp; [| inversion Hinterp].
  destruct v; inversion Hinterp; clear H0.
  destruct option_map as [(ins & sz)|] eqn: Hdecode_op; [| inversion Hinterp].
  destruct aexec_instr as [ rs' stk' stkb' m' |] eqn: Hexe; [| inversion Hinterp].

  eapply aexec_instr_inv in Hpc; eauto.
  destruct Hpc as (Hpc1 & Hpc_max & Hunchanged).
  unfold Ptrofs.of_int in Hload.
  rewrite Int.unsigned_repr in Hload.
  2:{ change Int.max_unsigned with Ptrofs.max_unsigned; lia. }
  rewrite Ptrofs.unsigned_repr in Hload.
  2:{ lia. }

  rewrite Hload_ins in Hload.
  injection Hload as Heq; subst i0.
  destruct Int.eq eqn: Heq; [| inversion Hsubst].
  apply Int.same_if_eq in Heq; subst i.
  unfold option_map in Hdecode_op.
  destruct decode_thumb eqn: Hdecode_t; inversion Hdecode_op; subst.
  rewrite Hexe.
  eapply IHnl with (ofs := ofs + 4) (jit_blk := jit_blk); eauto.
  clear - Hsubst Hunchanged.
  eapply code_subset_in_blk_unchange; eauto.
Qed.

Section Forward4.

Hypothesis _bpf_get_call: ident -> genv -> option fundef.
(*
Lemma jit_call_simpl_exec_bin_code_equiv:
  forall bl n v l0 ofs jit_blk m (rs rs' rs2: regset) m' brs1 c kl kv l
  (Hnth : nth_error bl n = Some (v, (ofs, l0)))
  (Hofs: (Z.of_nat (ofs + (List.length l0) * 4) < Int.max_unsigned)%Z)
  (Hsubst : code_subset_in_blk l0 ofs jit_blk m = true)
  (Hexe : exec_bin_code l0 ofs jit_blk rs m = Next rs' m')
  (Hpc_eq : Vint (Int.repr (Z.of_nat v)) = rs BPC)
  (Hreg_eq : forall r : reg,
          exists vi : val,
            eval_regmap r brs1 = vi /\ vi = rs (reg_to_breg r))
  (Hjit_blk : jit_arm_start_address = Vptr jit_blk Ptrofs.zero)
  (Hlen_max : Datatypes.length c <= 5000)
  (Hlen: List.length l0 < JITTED_LIST_MAX_LENGTH)
  (Hanalyzer : analyzer c = Some kl)
  (Hcombiner : combiner kl = Some bl)
  (Hconcat : concat_bin bl = (kv, l))
  (Hreg_inv: reg_inv (State rs m))
  (Hle_pc : v < Datatypes.length c),
    exists (pc3 : int) (brs3 : regmap) (m3 : mem) 
    (f3 : bpf_flag),
      match
        jit_call_simpl (kv_flatten kv (Datatypes.length c))
          (Int.repr (Z.of_nat v)) brs1 m
      with
      | Some (pc', rs'0, m'0) => Some (pc', rs'0, m'0, BPF_OK)
      | None => None
      end = Some (pc3, brs3, m3, f3) /\
      Vint pc3 = rs' BPC /\
      (forall r0 : reg,
       exists vi : val,
         eval_regmap r0 brs3 = vi /\ vi = rs' (reg_to_breg r0)) /\
      m3 = m' /\ f3 = BPF_OK.
Proof.
  intros.
  unfold jit_call_simpl.
  rewrite Hjit_blk; clear Hjit_blk.

  erewrite kv_flatten_property; eauto.

  unfold exec_bin_code in Hexe.
  unfold state_block_size in *.
  destruct Mem.alloc eqn: Halloc.
  destruct copy_to as [m1 | ] eqn: Hcopy_to; [| inversion Hexe].
  erewrite rbpf_copy_to_equiv; eauto.

  unfold bin_exec.
  change (Int.unsigned (Int.repr 52%Z)) with 52%Z.
  unfold stack_block_size in Hexe.
  destruct init_state as [ars1 stk1 stkb1 am | ]
    eqn: Hinit_state; [| inversion Hexe].

  simpl in Hinit_state.
  rewrite Ptrofs.add_zero_l in Hinit_state.

  assert (Hars_pc: ars1#PC = Cval (Vptr jit_blk
                   (Ptrofs.of_int (Int.repr
                            (Z.of_nat ofs))
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
  eapply code_subset_in_blk_copy_to_unchanged in Hsubst; eauto.
  eapply code_subset_in_blk_init_state_unchanged in Hsubst; eauto.


  destruct get_result_bool eqn: Hget_result; [| inversion Hexe].
  eapply jit_inv1 in Hsubst; eauto.

  eapply exec_bin_list_bin_interp in Hsubst; eauto.

  destruct Hsubst as (res & Hinterp).
  rewrite Hinterp.

  destruct copy_from as [rs1 | ] eqn: Hcopy_from; [| inversion Hexe].
  injection Hexe as Hrs1_eq Hm_eq; subst rs' m'.

  eapply copy_from_reg_inv in Hreg_inv; eauto.

  unfold reg_inv in Hreg_inv.
  specialize (Hreg_inv BPC).
  destruct Hreg_inv as (vpc & Hvpc_eq).
  symmetry in Hvpc_eq.
  eapply rbpf_copy_from_equiv in Hcopy_from; eauto.
  destruct Hcopy_from as (brs' & Hcopy_from & Hreg).
  exists vpc, brs', m, BPF_OK.
  rewrite Hcopy_from.
  split; [reflexivity |].
  split; [assumption |].
  split; [assumption |].
  split; reflexivity.
Qed. *)


Theorem backward_from_interpreter_simpl_to_ts:
  forall rs1 rs2 m1 m2 c kl bl kv l ge jit_blk mrs,
    step c (kv_flatten kv (List.length c)) (List.length c) rs1 (List.length mrs) mrs m1 =
      Some (rs2, m2, BPF_OK) ->

    jit_arm_start_address = Vptr jit_blk Ptrofs.zero ->
    code_subset_in_blk l 0 jit_blk m1 = true ->

    List.length c <= MAX_BPF_LIST_INPUT ->
    analyzer c = Some kl ->
    combiner kl = Some bl ->
    concat_bin bl = (kv, l) ->
    reg_inv (State rs1 m1) ->
    List.length l < JITTED_LIST_MAX_LENGTH ->

    exists t,
    bstep _bpf_get_call (memory_region_mapping mrs) c bl jit_blk ge
      (State rs1 m1) t (State rs2 m2).
Proof.
  intros rs1 rs2 m1 m2 c kl bl kv l ge jit_blk mrs Hstep
    Hjit_blk Hsubst Hlen_max Hanalyzer Hcombiner Hconcat Hreg_inv Hjit_len_max.
  unfold step in Hstep.
  unfold eval_ins in Hstep.
  destruct (rs1 BPC) as [|v_pc | v_l | v_f | v_s | v_b v_ofs] eqn: Hpc_eq;
    inversion Hstep; clear H0.
  destruct Int.cmpu eqn: Hlt; [| inversion Hstep].
  destruct nth_error eqn: Hnth; [| inversion Hstep].

  assert (Hpc_eq_nat: v_pc = (Int.repr (Z.of_nat (Z.to_nat (Int.unsigned v_pc))))). {

    unfold MAX_BPF_LIST_INPUT in Hlen_max.

    (**r pc1 <= List.length c because of find_instr = Some *)
    assert (Hle_pc: (Z.to_nat (Int.unsigned v_pc)) < List.length c). {
      apply nth_error_Some.
      intro HF.
      rewrite HF in Hnth.
      inversion Hnth.
    }
    rewrite Z2Nat.id.
    2:{ set (Int_unsigned_ge_zero v_pc) as Heq. lia. }

    rewrite Int.repr_unsigned; auto.
  }

  destruct decode_ind as [ins | ] eqn: Hdecode; [| inversion Hstep].
  destruct ins.
  - exists E0.
    assert (Hofs_eq: Ptrofs.to_int (Ptrofs.of_int o) = o). {
      apply Ptrofs.to_int_of_int.
      unfold Archi.ptr64.
      reflexivity.
    }

    unfold step_load_x_operation in Hstep.
    destruct check_mem as [ptr |] eqn: Hcheck_mem; [| inversion Hstep].
    eapply check_mem_prop in Hcheck_mem as Hmem; eauto.
    unfold rBPFValues.cmp_ptr32_null in Hstep.
    unfold Val.cmpu_bool in Hstep.
    destruct Hmem as [Hmem | Hnull].
    2:{ subst ptr.
      unfold Vnullptr, Archi.ptr64 in *.
      simpl in Hstep.
      rewrite Int.eq_true in Hstep.
      inversion Hstep.
    }

    destruct Hmem as (blk & ofs & Hptr & Hvalid1 & Hvalid2).
    subst ptr.
    unfold Vnullptr, Archi.ptr64 in *.
    rewrite Int.eq_true in Hstep.
    rewrite Hvalid1 in Hstep.
    simpl in Hstep.

    eapply bexec_step_internal_load with (v := (Z.to_nat (Int.unsigned v_pc)))
    (b := blk); eauto.
    + rewrite <- Hpc_eq_nat; auto.
    + unfold find_instr.
      rewrite Hnth.
      rewrite Hdecode.
      reflexivity.
    + unfold exec_load.
      unfold load_mem in Hstep.
      destruct Mem.loadv eqn: Hload.
      * destruct sizeOp2chunk; inversion Hstep; clear H0.
        { destruct v; inversion Hstep; clear H0. f_equal. }
        { destruct v; inversion Hstep; clear H0. f_equal. }
        { destruct v; inversion Hstep; clear H0. f_equal. }
      * destruct sizeOp2chunk; inversion Hstep.

  - exists E0.
    assert (Hofs_eq: Ptrofs.to_int (Ptrofs.of_int o) = o). {
      apply Ptrofs.to_int_of_int.
      unfold Archi.ptr64.
      reflexivity.
    }

    unfold step_store_operation in Hstep.
    destruct s0 as [src_r | src_i].
    {
      destruct check_mem as [ptr |] eqn: Hcheck_mem; [| inversion Hstep].
      eapply check_mem_prop in Hcheck_mem as Hmem; eauto.
      unfold rBPFValues.cmp_ptr32_null in Hstep.
      unfold Val.cmpu_bool in Hstep.
      destruct Hmem as [Hmem | Hnull].
      2:{ subst ptr.
        unfold Vnullptr, Archi.ptr64 in *.
        simpl in Hstep.
        rewrite Int.eq_true in Hstep.
        inversion Hstep.
      }

      destruct Hmem as (blk & ofs & Hptr & Hvalid1 & Hvalid2).
      subst ptr.
      unfold Vnullptr, Archi.ptr64 in *.
      rewrite Int.eq_true in Hstep.
      rewrite Hvalid1 in Hstep.
      simpl in Hstep.

      eapply bexec_step_internal_store with (v := (Z.to_nat (Int.unsigned v_pc)))
      (b := blk); eauto.
      + rewrite <- Hpc_eq_nat; auto.
      + unfold find_instr.
        rewrite Hnth.
        rewrite Hdecode.
        reflexivity.
      + unfold exec_store.
        unfold store_mem in Hstep.
        unfold eval_reg_imm.
        destruct Mem.storev eqn: Hload.
        * destruct sizeOp2chunk; inversion Hstep; clear H0; f_equal.
        * destruct sizeOp2chunk; inversion Hstep.
    }
    {
      destruct check_mem as [ptr |] eqn: Hcheck_mem; [| inversion Hstep].
      eapply check_mem_prop in Hcheck_mem as Hmem; eauto.
      unfold rBPFValues.cmp_ptr32_null in Hstep.
      unfold Val.cmpu_bool in Hstep.
      destruct Hmem as [Hmem | Hnull].
      2:{ subst ptr.
        unfold Vnullptr, Archi.ptr64 in *.
        simpl in Hstep.
        rewrite Int.eq_true in Hstep.
        inversion Hstep.
      }

      destruct Hmem as (blk & ofs & Hptr & Hvalid1 & Hvalid2).
      subst ptr.
      unfold Vnullptr, Archi.ptr64 in *.
      rewrite Int.eq_true in Hstep.
      rewrite Hvalid1 in Hstep.
      simpl in Hstep.

      eapply bexec_step_internal_store with (v := (Z.to_nat (Int.unsigned v_pc)))
      (b := blk); eauto.
      + rewrite <- Hpc_eq_nat; auto.
      + unfold find_instr.
        rewrite Hnth.
        rewrite Hdecode.
        reflexivity.
      + unfold exec_store.
        unfold store_mem in Hstep.
        unfold eval_reg_imm.
        destruct Mem.storev eqn: Hload.
        * destruct sizeOp2chunk; inversion Hstep; clear H0; f_equal.
        * destruct sizeOp2chunk; inversion Hstep.
    }
 
  - unfold BState.jit_call_simplb in Hstep.
    rewrite Hpc_eq in Hstep.
    destruct ListNat.index as [ofs|] eqn: Hkv_ofs; [| inversion Hstep].
    exists E0.
    assert (Hpc_eq1: rs1 BPC = Vint (Int.repr (Z.of_nat (Z.to_nat (Int.unsigned v_pc))))). {
      rewrite <- Hpc_eq_nat.
      auto.
    }

    assert (Hfind: find_instr (Z.to_nat (Int.unsigned v_pc)) c = Some (Palu32 a b s)). {
      unfold find_instr.
      rewrite Hnth.
      apply Hdecode.
    }

    assert (Heq: exists n nl,
      nth_error bl n = Some (Z.to_nat (Int.unsigned v_pc), (ofs, nl)) /\
      code_subset_in_blk nl ofs jit_blk m1 = true /\
      exec_bin_code nl ofs jit_blk rs1 m1 = Next rs2 m2 ). {
      unfold exec_bin_code.
      destruct Mem.alloc as (m3 & st_blk) eqn: Halloc.
      destruct copy_to as [m4 | ] eqn: Hcopy_to; [| inversion Hstep].
      unfold bin_exec in Hstep.
      rewrite Hjit_blk in Hstep.
      rewrite Int.unsigned_repr in Hstep; [
        | unfold stack_block_size; change Int.max_unsigned with 4294967295%Z; lia ].
      destruct init_state as [rs stk stkb m5 |] eqn: Hinit; [| inversion Hstep].

      eapply kv_flatten_property in Hkv_ofs; eauto.
      destruct Hkv_ofs as (nl & HIn & Hsubst1).
      apply In_nth_error in HIn; auto.
      destruct HIn as (n & HIn).
      exists n, nl.
      split; [assumption | ].
      split; [assumption | ].
      destruct bin_interp as [(res & m6) | ] eqn: Hinterp; [| inversion Hstep].
      eapply bin_interp_less_fuel with () in Hinterp; eauto.
      eapply bin_interp_exec_bin_list in Hinterp; eauto.
      ../..


 *)


      admit.
    }

    destruct Heq as (n & nl & Hnth1 & Hsubst1 & Hexe1).
    eapply bexec_step_alu32 with (v := (Z.to_nat (Int.unsigned v_pc))) (ofs := ofs); eauto.

  - 
Qed.
End Forward4.