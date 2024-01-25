From bpf.comm Require Import LemmaInt State MemRegion Regs Flag ListAsArray rBPFMemType.
From compcert Require Import Coqlib Integers Values AST Clight Memory Memtype.

From bpf.comm Require Import JITCall.
From bpf.clightlogic Require Import CommonLemma CommonLib Clightlogic.
From bpf.jit Require Import KeyValue2.
From bpf.jit.havm Require Import HAVMState.
From Coq Require Import ZArith List.
Open Scope Z_scope.
Import ListNotations.

Global Transparent Archi.ptr64.
Global Transparent Ctypes.intsize_eq.

Definition match_region_at_ofs (mr:memory_region) (state_blk mrs_blk ins_blk: block) (ofs : ptrofs) (m: mem)  : Prop :=
  (exists vl,  Mem.loadv AST.Mint32 m (Vptr mrs_blk ofs) = Some (Vint vl) /\ (start_addr mr) = Vint vl)    /\ (**r start_addr mr = Vint vl*)
    (exists vl,  Mem.loadv AST.Mint32 m (Vptr mrs_blk (Ptrofs.add ofs (Ptrofs.repr 4))) = Some (Vint vl) /\ (block_size mr) = Vint vl) /\ (**r block_size mr = Vint vl*)
    (exists vl,  Mem.loadv AST.Mint32 m (Vptr mrs_blk (Ptrofs.add ofs (Ptrofs.repr 8))) = Some (Vint vl) /\ correct_perm (block_perm mr)  vl) /\ (**r block_perm mr = Vint vl*)
    (exists b, Mem.loadv AST.Mptr  m (Vptr mrs_blk (Ptrofs.add ofs (Ptrofs.repr 12))) = Some (Vptr b Ptrofs.zero) /\ (block_ptr mr) = Vptr b Ptrofs.zero /\ (Mem.valid_block m b /\ b <> state_blk /\ b <> mrs_blk /\ b <> ins_blk)).


Definition match_list_region (m:mem) (state_blk mrs_blk ins_blk: block) (l:list memory_region) :=
  forall i, (0 <= i < List.length l)%nat -> match_region_at_ofs (List.nth i l default_memory_region) state_blk mrs_blk ins_blk (Ptrofs.repr (16 * Z.of_nat i)) m.

Definition match_regions (state_blk mrs_blk ins_blk: block) (st: hybrid_state) (m:mem) :=
  List.length (bpf_mrs st) = (mrs_num st) /\ (**r the number of bpf_mrs is exactly the mrs_num *)
  Z.of_nat (List.length (bpf_mrs st)) * 16 <= Ptrofs.max_unsigned /\ (**r there is not overflow *)
  match_list_region m state_blk mrs_blk ins_blk (bpf_mrs st).


Lemma match_regions_in:
  forall l mr m state_blk mrs_blk ins_blk
    (Hnth_error : In mr l)
    (Hmatch : match_list_region m state_blk mrs_blk ins_blk l),
      exists n, match_region_at_ofs mr state_blk mrs_blk ins_blk (Ptrofs.repr (16 * Z.of_nat n)) m.
Proof.
  unfold match_list_region.
  intros.
  apply In_nth_error in Hnth_error.
  destruct Hnth_error as (n & Hnth_error).
  apply nth_error_some_length in Hnth_error as Hlen.
  specialize (Hmatch n Hlen).
  destruct Hlen as ( _ & Hlen).
  apply nth_error_nth' with (d:= default_memory_region) in Hlen.
  rewrite Hlen in Hnth_error.
  inversion Hnth_error.
  subst.
  exists n; assumption.
Qed.

Definition match_list_ins (m:mem) (b: block) (l: list int64) :=
  forall i, (0 <= i < List.length l)%nat ->
    Mem.loadv AST.Mint64 m  (Vptr b (Ptrofs.repr (8 * (Z.of_nat i)))) = Some (Vlong (List.nth i l Int64.zero)).

Definition match_ins (ins_blk: block) (st: hybrid_state) (m:mem) :=
  List.length (input_ins st) = (input_len st) /\
  Z.of_nat (List.length (input_ins st)) * 8 <= Ptrofs.max_unsigned /\
  match_list_ins m ins_blk (input_ins st).

Definition match_list_kv (m:mem) (b: block) (l: ListKeyV.t) :=
  forall i, (0 <= i < List.length l)%nat ->
    Mem.loadv AST.Mint32 m  (Vptr b (Ptrofs.repr (8 * (Z.of_nat i)))) =
      Some (Vint (Int.repr (Z.of_nat (arm_ofs (List.nth i l empty_kv))))) /\
    Mem.loadv AST.Mint32 m  (Vptr b (Ptrofs.repr (8 * (Z.of_nat i) + 4))) =
      Some (Vint (Int.repr (Z.of_nat (alu32_ofs (List.nth i l empty_kv))))).

Definition match_kv (ins_blk: block) (st: hybrid_state) (m:mem) :=
  List.length (tp_kv st) = (input_len st) /\
  Z.of_nat (List.length (tp_kv st)) * 8 <= Ptrofs.max_unsigned /\
  match_list_kv m ins_blk (tp_kv st).

Definition match_list_jit (m:mem) (b: block) (l: list int) :=
  forall i, (0 <= i < List.length l)%nat ->
    Mem.loadv AST.Mint32 m  (Vptr b (Ptrofs.repr (4 * (Z.of_nat i)))) = Some (Vint (List.nth i l Int.zero)).

Definition match_jit (ins_blk: block) (st: hybrid_state) (m:mem) :=
  List.length (input_ins st) = JITTED_LIST_MAX_LENGTH /\
  (List.length (input_ins st) >= (tp_bin_len st))%nat /\
  match_list_jit m ins_blk (tp_bin st).

(* Permission Lemmas: deriving from riot-rbpf/MemInv.v *)
Lemma range_perm_included:
  forall m b p lo hi ofs_lo ofs_hi, 
    lo <= ofs_lo -> ofs_lo < ofs_hi -> ofs_hi <= hi ->  (**r `<` -> `<=` *)
    Mem.range_perm m b lo hi Cur p ->
      Mem.range_perm m b ofs_lo ofs_hi Cur p.
Proof.
  intros.
  apply (Mem.range_perm_implies _ _ _ _ _ p _); [idtac | constructor].
  unfold Mem.range_perm in *; intros.
  apply H2.
  lia.
Qed.

Definition match_region (st_blk mrs_blk ins_blk : block) (mr: memory_region) (v: val) (st: hybrid_state) (m:Memory.Mem.mem) :=
  exists o, v = Vptr mrs_blk o /\
              match_region_at_ofs mr st_blk mrs_blk ins_blk o m.

Lemma same_memory_match_region :
  forall st_blk mrs_blk ins_blk st st' m m' mr v
         (UMOD : unmodifies_effect ModNothing m m' st st'),
    match_region st_blk mrs_blk ins_blk mr v st m ->
    match_region st_blk mrs_blk ins_blk mr v st' m'.
Proof.
  intros.
  unfold match_region in *.
  destruct H as (o & E & MR).
  exists o.
  split; auto.
  unfold match_region_at_ofs in *.
  unfold unmodifies_effect in UMOD.
  destruct UMOD; subst.
  repeat rewrite <- UMOD by (simpl ; tauto).
  intuition.
Qed.

Lemma upd_preserves_match_list_ins:
  forall l chunk m0 m1 st_blk ins_blk ofs0 vl
  (Hstore : Mem.store chunk m0 st_blk ofs0 vl = Some m1)
  (mem_regs : match_list_ins m0 ins_blk l)
  (Hneq_blk : st_blk <> ins_blk),
    match_list_ins m1 ins_blk l.
Proof.
  intro l.
  induction l.
  unfold match_list_ins in *.
  intros.
  simpl in H.
  lia.

  intros; simpl in *.
  unfold match_list_ins in *.
  intros.
  specialize (mem_regs i H).
  unfold Mem.loadv in *.
  rewrite <- mem_regs.
  eapply Mem.load_store_other; eauto.
Qed.

Lemma upd_preserves_match_list_kv:
  forall l chunk m0 m1 st_blk ins_blk ofs0 vl
  (Hstore : Mem.store chunk m0 st_blk ofs0 vl = Some m1)
  (mem_regs : match_list_kv m0 ins_blk l)
  (Hneq_blk : st_blk <> ins_blk),
    match_list_kv m1 ins_blk l.
Proof.
  intro l.
  induction l.
  unfold match_list_kv in *.
  intros.
  simpl in H.
  lia.

  intros; simpl in *.
  unfold match_list_kv in *.
  intros.
  specialize (mem_regs i H).
  unfold Mem.loadv in *.
  destruct mem_regs as (Heq & Heq1).
  rewrite <- Heq.
  rewrite <- Heq1.
  split; eapply Mem.load_store_other; eauto.
Qed.

Lemma upd_preserves_match_list_jit:
  forall l chunk m0 m1 st_blk ins_blk ofs0 vl
  (Hstore : Mem.store chunk m0 st_blk ofs0 vl = Some m1)
  (mem_regs : match_list_jit m0 ins_blk l)
  (Hneq_blk : st_blk <> ins_blk),
    match_list_jit m1 ins_blk l.
Proof.
  intro l.
  induction l.
  unfold match_list_jit in *.
  intros.
  simpl in H.
  lia.

  intros; simpl in *.
  unfold match_list_jit in *.
  intros.
  specialize (mem_regs i H).
  unfold Mem.loadv in *.
  rewrite <- mem_regs.
  eapply Mem.load_store_other; eauto.
Qed.

Lemma upd_preserves_match_list_region:
  forall l chunk m0 m1 st_blk mrs_blk ins_blk b ofs0 vl
  (Hstore : Mem.store chunk m0 b ofs0 vl = Some m1)
  (mem_regs : match_list_region m0 st_blk mrs_blk ins_blk l)
  (Hneq_blk : b <> mrs_blk),
    match_list_region m1 st_blk mrs_blk ins_blk l.
Proof.
  intro l.
  induction l;
  unfold match_list_region in *.
  intros; simpl in *.
  lia.

  intros.
  unfold match_region_at_ofs in *.
  specialize (mem_regs i H).
  destruct mem_regs as  ((vl0 & Hload0 & Heq0) & (vl1 & Hload1 & Heq1) & (vl2 & Hload2 & Heq2) & (blk3 & Hload3 & Heq_ptr)).

  split.
  exists vl0; rewrite <- Hload0; split; [
  eapply Mem.load_store_other; eauto | assumption].

  split.
  exists vl1; rewrite <- Hload1; split; [
  eapply Mem.load_store_other; eauto | assumption].

  split.
  exists vl2; rewrite <- Hload2; split; [
  eapply Mem.load_store_other; eauto | assumption].

  exists blk3; rewrite <- Hload3; split; [
  eapply Mem.load_store_other; eauto | ].
  intuition.
  eapply Mem.store_valid_block_1; eauto.
Qed.

Close Scope Z_scope.