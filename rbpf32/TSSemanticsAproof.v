From compcert.lib Require Import Integers Coqlib Maps.
From compcert.common Require Import AST Values Events Globalenvs Memory Memtype Events Smallstep.
From compcert.cfrontend Require Import Ctypes. (*
From compcert.backend Require Import Locations. *)
From compcert.arm Require Import ABinSem.
From Coq Require Import ZArith Lia List.

From bpf.rbpf32 Require Import TSSyntax TSDecode TSSemantics TSSemanticsA Analyzer.

Open Scope nat_scope.
Import ListNotations.

Section JITBackwardSimulationProof.

Hypothesis _bpf_get_call: ident -> genv -> option fundef.
Hypothesis memory_region_map: mem -> permission -> memory_chunk -> val -> block -> ptrofs -> Prop.

Lemma exec_alu32_list_code_subset:
  forall l ge bpf_get_call mem_map c v rs m rs' m'
    (HMAX: List.length c <= MAX_BPF_LIST_INPUT)
    (HPC: rs BPC = Vint (Int.repr (Z.of_nat v)))
    (HEXE : exec_alu32_list l rs m = Next rs' m')
    (HSUB : code_subset l v c = true),
    star (step bpf_get_call mem_map c) ge (State rs m) E0 (State rs' m').
Proof.
  induction l; simpl; intros.
  - inversion HEXE; subst.
    eapply star_refl; eauto.
  - destruct a; inversion HEXE.
    destruct exec_alu32 as [rs1 m1 | ] eqn: He; [| inversion HEXE].
    destruct nth_error as [ins | ] eqn: Hnth; [| inversion HSUB].
    destruct decode_ind as [bpf_ins | ] eqn: Hbpf; [| inversion HSUB].
    destruct instruction_alu32_eqb eqn: Halu32; [| inversion HSUB].

    assert (HLE: v < List.length c). {
      clear - Hnth.
      eapply nth_error_Some; eauto.
      rewrite Hnth. intro HF; inversion HF.
    }

    unfold MAX_BPF_LIST_INPUT in HMAX.

    assert (HPC1 : rs1 BPC = Vint (Int.repr (Z.of_nat (S v)))). {
      clear - HMAX HPC HLE He.
      unfold exec_alu32 in He.
      destruct eval_alu32 as [va | ] eqn: HA; [| inversion He].
      unfold nextinstr in He.
      destruct va as [| vi | | | |]; inversion He.
      rewrite BPregmap.gss.
      rewrite ! BPregmap.gso. 2:{ clear; intro HF; inversion HF. }
      rewrite HPC.
      clear - HMAX HLE. (**r we need to show v is less than int_max *)
      unfold Val.add, Vone.
      unfold Int.add, Int.one.
      f_equal.
      rewrite Int.unsigned_repr. 2:{ change Int.max_unsigned with 4294967295%Z; lia. }
      change (Int.unsigned (Int.repr 1)) with 1%Z.
      replace (Z.of_nat v + 1)%Z with (Z.of_nat (S v)) by lia.
      f_equal.
    }
    eapply star_left with (t1 := E0); eauto.
    eapply exec_step_alu32; eauto.

    unfold find_instr.
    rewrite Hnth.
    rewrite Hbpf.
    clear - Halu32.
    unfold instruction_alu32_eqb in Halu32.
    destruct bpf_ins; inversion Halu32.
    clear H0.
    rewrite ! andb_true_iff in Halu32.
    destruct Halu32 as ((Heq1 & Heq2) & Heq3).
    rewrite <- aluOp_eqb_true in Heq1.
    rewrite <- breg_eqb_true in Heq2.
    subst.
    destruct s.
    + destruct s0; [| inversion Heq3].
      rewrite <- breg_eqb_true in Heq3.
      subst; auto.
    + destruct s0; [inversion Heq3 | ].
      apply Int.same_if_eq in Heq3.
      subst; auto.
Qed.

Theorem astep_backward_simulation:
  forall ge bpf_get_call mem_map c kl rs0 m0 t rs1 m1,
    astep bpf_get_call mem_map c kl ge (State rs0 m0) t (State rs1 m1) ->
    List.length c <= MAX_BPF_LIST_INPUT ->
    analyzer c = Some kl ->
      star (step bpf_get_call mem_map c) ge (State rs0 m0) t (State rs1 m1).
Proof.
  induction 1.
  - (**r exec_step_alu32 *)
    rename H into PC.
    rename H0 into Hfind.
    rename H1 into Hnth.
    rename H2 into HEXE.
    intros HINV HA.
    apply nth_error_In in Hnth.
    eapply analyzer_code_subset with (ep := v) (l := l) in HA; eauto.
    eapply exec_alu32_list_code_subset; eauto.
  - intros; eapply star_one; eapply exec_step_jmp_always; eauto.
  - intros; eapply star_one; eapply exec_step_jmp_cond; eauto.
  - intros; eapply star_one; eapply exec_step_internal_load; eauto.
  - intros; eapply star_one; eapply exec_step_internal_store; eauto.
  - intros; eapply star_one; eapply exec_step_external; eauto.
Qed.

End JITBackwardSimulationProof.