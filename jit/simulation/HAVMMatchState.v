From bpf.comm Require Import LemmaInt State MemRegion Regs Flag ListAsArray rBPFMemType.
From compcert Require Import Coqlib Integers Values AST Clight Memory Memtype.

From bpf.comm Require Import JITCall.
From bpf.clightlogic Require Import CommonLemma CommonLib Clightlogic.
From bpf.jit Require Import KeyValue2.
From bpf.jit.havm Require Import HAVMState.
From bpf.jit.simulation Require Import MatchStateComm.
From Coq Require Import ZArith List.
Open Scope Z_scope.
Import ListNotations.

Class special_blocks : Type :=
  { st_blk : block;
    kv_blk  : block;
    jit_blk  : block;
    mrs_blk  : block;
    ins_blk  : block }.

Section S.

  Context {Blocks : special_blocks}.

  Definition match_registers  (rmap:regmap) (bl_reg:block) (m : mem) : Prop:=
    forall (r:reg),
    exists vi, Mem.loadv Mint32 m (Vptr bl_reg (Ptrofs.repr (4 * (id_of_reg r)))) = Some (Vint vi) /\
            Vint vi = eval_regmap r rmap.

(**r memory_layout: 11*4 + 4 * 9 = 80

Record hybrid_state := mkst {
  regs_st     : regmap;
  pc_loc      : int;
  flag        : bpf_flag;
  mrs_num     : nat;
  bpf_mrs     : MyMemRegionsType;
  input_len   : nat;
  input_ins   : List64AsArray.t;(**r rBPF binary instructions *)
  tp_kv       : ListKeyV.t;
  tp_bin_len  : nat;  (**r the number of all jitted instructions *)
  tp_bin      : List32.t;
  bpf_m       : Memory.mem;
}.

*)

  Record match_state  (st: hybrid_state) (m: mem) : Prop :=
    {
      munchange: Mem.unchanged_on (fun b _ => b <> st_blk /\ b <> mrs_blk /\
                    b <> ins_blk /\ b <> jit_blk /\ b <> kv_blk) (bpf_m st) m;
      mregs    : match_registers (regs_st st) st_blk m;
      mpc      : Mem.loadv AST.Mint32 m (Vptr st_blk (Ptrofs.repr 44)) = Some (Vint  (pc_loc st));
      mflags   : Mem.loadv AST.Mint32 m (Vptr st_blk (Ptrofs.repr 48)) = Some (Vint  (int_of_flag (flag st)));
      mmrs_num : Mem.loadv AST.Mint32 m (Vptr st_blk (Ptrofs.repr 52)) = Some (Vint  (Int.repr (Z.of_nat (mrs_num st)))) /\
                 (Z.of_nat(mrs_num st)) >= 1;
      mem_regs : Mem.loadv AST.Mptr m (Vptr st_blk (Ptrofs.repr 56)) = Some (Vptr mrs_blk (Ptrofs.repr 0)) /\
                  match_regions st_blk mrs_blk ins_blk st m;
      mins_len : Mem.loadv AST.Mint32 m (Vptr st_blk (Ptrofs.repr 60)) = Some (Vint (Int.repr (Z.of_nat (input_len st)))) /\
                  Z.of_nat (input_len st) >= 1;
      mins     : Mem.loadv AST.Mptr m (Vptr st_blk (Ptrofs.repr 64)) = Some (Vptr ins_blk (Ptrofs.repr 0)) /\ match_ins ins_blk st m;
      mkv      : Mem.loadv AST.Mptr m (Vptr st_blk (Ptrofs.repr 68)) = Some (Vptr kv_blk (Ptrofs.repr 0)) /\ match_kv kv_blk st m;
      mbin_len : Mem.loadv AST.Mint32 m (Vptr st_blk (Ptrofs.repr 72)) = Some (Vint (Int.repr (Z.of_nat (tp_bin_len st)))) /\
                  Z.of_nat (tp_bin_len st) >= 1;
      mbin     : Mem.loadv AST.Mptr m (Vptr st_blk (Ptrofs.repr 76)) = Some (Vptr jit_blk (Ptrofs.repr 0)) /\
                  match_jit jit_blk st m /\ jit_state_block = st_blk /\ jit_arm_block = jit_blk;
      mperm    : Mem.range_perm m st_blk 0 80 Cur Freeable /\
                 Mem.range_perm m mrs_blk   0 (Z.of_nat (mrs_num st)) Cur Freeable /\
                 Mem.range_perm m ins_blk   0 (Z.of_nat (input_len st)) Cur Readable /\
                 Mem.range_perm m kv_blk 0 (Z.of_nat (input_len st)) Cur Readable /\
                 Mem.range_perm m jit_blk 0 (Z.of_nat (tp_bin_len st)) Cur Readable;
      minvalid : (~Mem.valid_block (bpf_m st) st_blk /\
                  ~Mem.valid_block (bpf_m st) mrs_blk /\
                  ~Mem.valid_block (bpf_m st) ins_blk /\
                  ~Mem.valid_block (bpf_m st) kv_blk /\
                  ~Mem.valid_block (bpf_m st) jit_blk) /\
                 (NoDup [st_blk; mrs_blk; ins_blk; kv_blk; jit_blk]) /\
                 (forall b, b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk /\ b <> jit_blk /\ b <> kv_blk ->
                  Mem.valid_block m b -> Mem.valid_block (bpf_m st) b);
    }.

End S.

(** Permission Lemmas: upd_pc *)
Lemma upd_pc_write_access:
  forall m0 {bl:special_blocks} st
    (Hst: match_state  st m0),
    Mem.valid_access m0 Mint32 st_blk 44 Writable.
Proof.
  intros; unfold Mem.valid_access; destruct Hst; clear - mem_regs0 mperm0; simpl in mem_regs0.
  unfold match_regions in *.
  destruct mperm0 as (mperm0 & _ & _).
  apply (Mem.range_perm_implies _ _ _ _ _ _ Writable) in mperm0; [idtac | constructor].

  unfold size_chunk, align_chunk.
  split.
  - simpl; apply (range_perm_included _ _ Writable _ _ 44 48) in mperm0; [assumption | lia | lia | idtac].
    lia.
  - change 44 with (11 * 4). apply Z.divide_factor_r.
Qed.

Lemma upd_pc_store:
  forall m0 {S: special_blocks} pc st
    (Hst: match_state  st m0),
    exists m1,
    Mem.store AST.Mint32 m0 st_blk 44 (Vint pc) = Some m1.
Proof.
  intros.
  apply upd_pc_write_access  in Hst.
  apply (Mem.valid_access_store _ _ _ _ (Vint pc)) in Hst.
  destruct Hst as (m2 & Hstore).
  exists m2; assumption.
Qed.

Lemma upd_flags_write_access:
  forall m0 {S:special_blocks} st
    (Hst: match_state  st m0),
    Mem.valid_access m0 Mint32 st_blk 48 Writable.
Proof.
  intros; unfold Mem.valid_access; destruct Hst; clear - mperm0; simpl in mperm0.
  destruct mperm0 as (mperm0 & _ & _).
  apply (Mem.range_perm_implies _ _ _ _ _ _ Writable) in mperm0; [idtac | constructor].

  unfold size_chunk, align_chunk.
  split.
  - simpl.
    apply (range_perm_included _ _ Writable _ _ 48 52) in mperm0; [assumption | lia | lia | lia].
  - change 48 with (12 * 4). apply Z.divide_factor_r.
Qed.

Lemma upd_flags_store:
  forall m0 {S: special_blocks} st v
    (Hst: match_state  st m0),
    exists m1,
    Mem.store AST.Mint32 m0 st_blk 48 (Vint v) = Some m1.
Proof.
  intros.
  apply (upd_flags_write_access _ _ ) in Hst.
  apply (Mem.valid_access_store _ _ _ _ (Vint v)) in Hst.
  destruct Hst as (m2 & Hstore).
  exists m2; assumption.
Qed.

(** Permission Lemmas: upd_regs *)
Lemma upd_regs_write_access:
  forall m0 {S: special_blocks} st r
    (Hst: match_state  st m0),
    Mem.valid_access m0 Mint32 st_blk (4 * (id_of_reg r)) Writable.
Proof.
  intros; unfold Mem.valid_access; destruct Hst; clear - mperm0; simpl in mperm0.
  destruct mperm0 as (mperm0 & _ & _).
  apply (Mem.range_perm_implies _ _ _ _ _ _ Writable) in mperm0; [idtac | constructor].
  assert (H: 0<= Z.of_nat (mrs_num st)). { apply Nat2Z.is_nonneg. }
  apply (range_perm_included _ _ Writable _ _ 0 44) in mperm0; [idtac | lia | lia | lia].

  unfold id_of_reg.
  unfold size_chunk, align_chunk.
  split.
  - apply (range_perm_included _ _ Writable _ _ (4 * (id_of_reg r)) (4 * (id_of_reg r +1))) in mperm0;
  destruct r; simpl in *; try lia; try assumption.
  - apply Z.divide_factor_l.
Qed.

Lemma upd_regs_store:
  forall m0 {S: special_blocks} st r v
    (Hst: match_state  st m0),
    exists m1,
    Mem.store AST.Mint32 m0 st_blk (4 * (id_of_reg r)) (Vint v) = Some m1.
Proof.
  intros.
  apply upd_regs_write_access with (r:=r) in Hst.
  apply (Mem.valid_access_store _ _ _ _ (Vint v)) in Hst.
  destruct Hst as (m2 & Hstore).
  exists m2; assumption.
Qed.

(**r a set of lemmas say upd_reg/flag/pc... don't change the memory/regs/flag/pc of rbpf *)

Lemma upd_reg_same_mem:
  forall st0 r vl,
    bpf_m st0 = bpf_m (upd_reg r vl st0).
Proof.
  unfold upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_reg_same_pc:
  forall st0 r vl,
    pc_loc st0 = pc_loc (upd_reg r vl st0).
Proof.
  unfold upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_reg_same_flag:
  forall st0 r vl,
    flag st0 = flag (upd_reg r vl st0).
Proof.
  unfold upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_reg_same_mrs:
  forall st0 r vl,
    bpf_mrs st0 = bpf_mrs (upd_reg r vl st0).
Proof.
  unfold upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_reg_same_mrs_num:
  forall st0 r vl,
    mrs_num st0 = mrs_num (upd_reg r vl st0).
Proof.
  unfold upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_reg_same_ins:
  forall st0 r vl,
    input_ins st0 = input_ins (upd_reg r vl st0).
Proof.
  unfold upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_reg_same_ins_len:
  forall st0 r vl,
    input_len st0 = input_len (upd_reg r vl st0).
Proof.
  unfold upd_reg.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_mem:
  forall st0 pc,
    bpf_m st0 = bpf_m (upd_pc pc st0).
Proof.
  unfold upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_regs:
  forall st0 pc,
    regs_st st0 = regs_st (upd_pc pc st0).
Proof.
  unfold upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_flag:
  forall st0 pc,
    flag st0 = flag (upd_pc pc st0).
Proof.
  unfold upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_mrs:
  forall st0 pc,
    bpf_mrs st0 = bpf_mrs (upd_pc pc st0).
Proof.
  unfold upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_mrs_num:
  forall st0 pc,
    mrs_num st0 = mrs_num (upd_pc pc st0).
Proof.
  unfold upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_ins:
  forall st0 pc,
    input_ins st0 = input_ins (upd_pc pc st0).
Proof.
  unfold upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_ins_len:
  forall st0 pc,
    input_len st0 = input_len (upd_pc pc st0).
Proof.
  unfold upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_tp_kv:
  forall st pc,
    tp_kv st = (tp_kv (upd_pc pc st)).
Proof.
  unfold upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_tp_bin_len:
  forall st pc,
    tp_bin_len st = (tp_bin_len (upd_pc pc st)).
Proof.
  unfold upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_pc_same_tp_bin:
  forall st pc,
    tp_bin st = (tp_bin (upd_pc pc st)).
Proof.
  unfold upd_pc.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_mem:
  forall st0 f,
    bpf_m st0 = bpf_m (upd_flag f st0).
Proof.
  unfold upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_regs:
  forall st0 f,
    regs_st st0 = regs_st (upd_flag f st0).
Proof.
  unfold upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_pc:
  forall st0 f,
    pc_loc st0 = pc_loc (upd_flag f st0).
Proof.
  unfold upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_mrs:
  forall st0 f,
    bpf_mrs st0 = bpf_mrs (upd_flag f st0).
Proof.
  unfold upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_mrs_num:
  forall st0 f,
    mrs_num st0 = mrs_num (upd_flag f st0).
Proof.
  unfold upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_ins:
  forall st0 f,
    input_ins st0 = input_ins (upd_flag f st0).
Proof.
  unfold upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_ins_len:
  forall st0 f,
    input_len st0 = input_len (upd_flag f st0).
Proof.
  unfold upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_tp_kv:
  forall st0 f,
    tp_kv st0 = tp_kv (upd_flag f st0).
Proof.
  unfold upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_tp_bin:
  forall st0 f,
    tp_bin st0 = tp_bin (upd_flag f st0).
Proof.
  unfold upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_flag_same_tp_bin_len:
  forall st0 f,
    tp_bin_len st0 = tp_bin_len (upd_flag f st0).
Proof.
  unfold upd_flag.
  intros.
  reflexivity.
Qed.

Lemma upd_unchanged_on:
  forall st m0 m1 {S:special_blocks} chunk ofs vl
  (Hst    : match_state  st m0)
  (Hstore : Mem.store chunk m0 st_blk ofs vl = Some m1),
    Mem.unchanged_on (fun b _ => b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk) m0 m1.
Proof.
  intros.
  destruct Hst.
  eapply Mem.store_unchanged_on.
  rewrite Hstore.
  reflexivity.
  intros.
  intro.
  destruct H0 as (H0 & _).
  apply H0; reflexivity.
Qed.

Lemma upd_reg_preserves_match_state:
  forall st0 st1 m0 m1 {S:special_blocks} r vi
  (Hst    : match_state  st0 m0)
  (Hst1   : upd_reg r (Vint vi) st0 = st1)
  (Hstore : Mem.store AST.Mint32 m0 st_blk (4 * id_of_reg r) (Vint vi) = Some m1),
    match_state  st1 m1.
Proof.
  intros.
  subst.
  set (Hst' := Hst).
  destruct Hst'.
  split; unfold Mem.loadv in *.
  -
    rewrite <- (upd_reg_same_mem _ r (Vint vi)).
    assert (Hunchanged_on': Mem.unchanged_on (fun (b : block) (_ : Z) =>
      b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk /\ b <> jit_blk /\ b <> kv_blk) m0 m1). {
      eapply Mem.store_unchanged_on; eauto.
      intros.
      intro.
      destruct H0 as (H0 & _).
      apply H0; reflexivity.
    }
    apply Mem.unchanged_on_trans with(m2:= m0); auto.
  - unfold match_registers in *.
    intros.
    specialize (mregs0 r0).
    destruct mregs0 as (vl0 & mregs0 & mregs1).
    unfold Mem.loadv, Ptrofs.add in *.
    rewrite Ptrofs_unsigned_repr_id_of_reg in *.

    destruct (reg_eq r0 r).
    + (**r case: r0 = r *)
      subst.
      exists vi.
      split.
      * assert (Hload_result: Val.load_result Mint32 (Vint vi) = (Vint vi)) by reflexivity.
        rewrite <- Hload_result.
        eapply Mem.load_store_same with (m1 := m0) (m2 := m1); eauto.
      * unfold upd_reg; simpl.
        rewrite eval_upd_regmap_same.
        reflexivity.
    +
      exists vl0.
      unfold upd_reg, regs_st.

      rewrite eval_upd_regmap_other.
      split.
      2:{
        rewrite mregs1.
        reflexivity.
      }
      rewrite <- mregs0.
      eapply Mem.load_store_other; eauto.
      right.
      2:{ assumption. }
      destruct r0, r; simpl; [try (exfalso; apply n; reflexivity) || (try left; lia) || (try right; lia) ..].
  -
    rewrite <- (upd_reg_same_pc _ r (Vint vi)).
    rewrite <- mpc0.
    eapply Mem.load_store_other; eauto.
    right; right.
    unfold id_of_reg; simpl.
    change (Ptrofs.unsigned (Ptrofs.repr 44)) with 44.
    destruct r; try lia.
  - rewrite <- (upd_reg_same_flag _ r (Vint vi)).
    rewrite <- mflags0.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n; [| try simpl; lia].
    unfold id_of_reg; simpl; destruct r; try lia.
  - rewrite <- (upd_reg_same_mrs_num _ r (Vint vi)).
    destruct mmrs_num0 as (Hload & Hge).
    split; [| assumption].
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    unfold size_chunk.
    assert (Hle_104: 4 * id_of_reg r + 4 <= 52). { unfold id_of_reg; destruct r; lia. }
    rewrite Ptrofs_unsigned_repr_n; [| try simpl; lia].
    assumption.
  - unfold match_regions in *.
    destruct mem_regs0 as (Hload & mrs_len & mrs_max & mem_regs0).
    rewrite <- (upd_reg_same_mrs _ r (Vint vi)).

    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    unfold id_of_reg, size_chunk; destruct r; lia.

    split; [assumption | ].
    split; [assumption | ].
    destruct minvalid0 as (_ & minvalid0 & _).
    eapply upd_preserves_match_list_region; eauto.
    inversion minvalid0.
    intro HF.
    apply H1.
    rewrite HF.
    left; reflexivity.
  - simpl.
    destruct mins_len0 as (mins_len0 & mins_len1).
    split; [| assumption].

    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    rewrite <- mins_len0.
    eapply Mem.load_store_other; eauto.
    right; right.
    unfold id_of_reg, size_chunk; destruct r; lia.
  - (**r match_ins *)
    unfold match_ins.
    unfold match_ins in mins0.
    destruct mins0 as (Hload & mins_len & mins_max & mins0).
    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    unfold id_of_reg, size_chunk; destruct r; lia.

    split; [assumption | ].
    split; [assumption | ].
    assert (Hins_eq : input_ins (upd_reg r (Vint vi) st0) = input_ins st0). {
      unfold upd_reg.
      simpl.
      reflexivity.
    }
    rewrite Hins_eq; clear Hins_eq.
    destruct minvalid0 as (_ & minvalid0 & _).
    eapply upd_preserves_match_list_ins; eauto.
    rewrite NoDup_cons_iff in minvalid0.
    intro HF.
    destruct minvalid0 as (HIn & _).
    apply HIn.
    rewrite HF.
    right.
    left; reflexivity.

  - unfold match_kv.
    unfold match_kv in mkv0.
    destruct mkv0 as (Hload & mins_len & mins_max & mkv0).
    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    unfold id_of_reg, size_chunk; destruct r; lia.

    split; [assumption | ].
    split; [assumption | ].
    assert (Hins_eq : tp_kv (upd_reg r (Vint vi) st0) = tp_kv st0). {
      unfold upd_reg.
      simpl.
      reflexivity.
    }
    rewrite Hins_eq; clear Hins_eq.
    destruct minvalid0 as (_ & minvalid0 & _).
    eapply upd_preserves_match_list_kv; eauto.
    rewrite NoDup_cons_iff in minvalid0.
    intro HF.
    destruct minvalid0 as (HIn & _).
    apply HIn.
    rewrite HF.
    right. right.
    left; reflexivity.

  - simpl.
    destruct mbin_len0 as (mbin_len0 & mbin_len1).
    split; [| assumption].

    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    rewrite <- mbin_len0.
    eapply Mem.load_store_other; eauto.
    right; right.
    unfold id_of_reg, size_chunk; destruct r; lia.
  - (**r match_ins *)
    unfold match_jit.
    unfold match_jit in mbin0.
    destruct mbin0 as (Hload & (mins_len & mins_max & mbin0) & Hblk1 & Hblk2).
    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    unfold id_of_reg, size_chunk; destruct r; lia.
    assert (Hins_eq : tp_bin (upd_reg r (Vint vi) st0) = tp_bin st0). {
      unfold upd_reg.
      simpl.
      reflexivity.
    }
    rewrite Hins_eq; clear Hins_eq.

    split.
    split; [assumption | ].
    split; [assumption | ].
    destruct minvalid0 as (_ & minvalid0 & _).
    eapply upd_preserves_match_list_jit; eauto.
    rewrite NoDup_cons_iff in minvalid0.
    intro HF.
    destruct minvalid0 as (HIn & _).
    apply HIn.
    rewrite HF.
    right. right. right.
    left; reflexivity.

    split; assumption.

  - clear - mperm0 Hstore.
    unfold Mem.range_perm in *.
    destruct mperm0 as (mperm0 & mperm1 & mperm2 & mperm3 & mperm4).
    split; [ intros | ].
    { eapply Mem.perm_store_1; eauto.
    }
    rewrite <- upd_reg_same_mrs_num in *.
    split; [ intros | ].
    {
      eapply Mem.perm_store_1; eauto.
    }

    split; [ intros | ].
    { eapply Mem.perm_store_1; eauto.
    }

    split; [ intros | ].
    { eapply Mem.perm_store_1; eauto.
    }

    intros.
    eapply Mem.perm_store_1; eauto.
  - rewrite <- upd_reg_same_mem.
    intuition.
    apply H21; auto.
    eapply Mem.store_valid_block_2; eauto.
Qed.


Lemma upd_pc_preserves_match_state:
  forall st0 st1 m0 m1 {S:special_blocks} pc
  (Hst    : match_state  st0 m0)
  (Hst1   : upd_pc pc st0 = st1)
  (Hstore : Mem.store AST.Mint32 m0 st_blk 44 (Vint (Int.add (pc_loc st0) pc)) = Some m1),
    match_state  st1 m1.
Proof.
  intros.
  subst.
  set (Hst' := Hst).
  split.
  -
    destruct Hst' as (Hunchanged_on, _, _, _, _, _, _, _, _, _, _, _, _).
    rewrite <- upd_pc_same_mem.
    assert (Hunchanged_on': Mem.unchanged_on (fun (b : block) (_ : Z) =>
      b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk /\ b <> jit_blk /\ b <> kv_blk) m0 m1). {
      eapply Mem.store_unchanged_on; eauto.
      intros.
      intro.
      destruct H0 as(H0 & _).
      apply H0; reflexivity.
    }
    apply Mem.unchanged_on_trans with(m2:= m0); auto.
  -
    destruct Hst' as (_ , Hregs, _, _, _, _, _, _, _, _, _, _, _).
    rewrite <- upd_pc_same_regs.
    unfold match_registers in *.
    intros.
    specialize (Hregs r).
    destruct Hregs as (vl & Hload & Hvl_eq).
    exists vl.
    split; [| assumption].
    rewrite <- Hload.
    unfold Mem.loadv.
    eapply Mem.load_store_other.
    apply Hstore.
    right; left.
    unfold Ptrofs.add in *.
    unfold size_chunk.
    rewrite Ptrofs_unsigned_repr_id_of_reg in *.
    unfold id_of_reg; destruct r; lia.
  -
    destruct Hst' as (_ , _, Hpc, _, _, _, _, _, _, _, _, _, _).
    unfold Mem.loadv in *.
    change (Ptrofs.unsigned (Ptrofs.repr 44)) with 44 in *.
    apply Mem.load_store_same in Hstore.
    rewrite Hstore.
    unfold Val.load_result.
    unfold upd_pc; simpl.
    reflexivity.
  -
    destruct Hst' as (_ , _, _, Hflag, _, _, _, _, _, _, _, _, _).
    rewrite <- upd_pc_same_flag.
    rewrite <- Hflag.
    eapply Mem.load_store_other.
    apply Hstore.
    right; right.
    rewrite Ptrofs_unsigned_repr_n; [| try simpl; lia].
    reflexivity.
  - 
    destruct Hst' as (_ , _, _, _, (Hmrs_len & Hge), _, _, _, _, _, _, _, _).
    rewrite <- upd_pc_same_mrs_num.
    split; [| assumption].
    rewrite <- Hmrs_len.
    simpl.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
  -
    destruct Hst' as (_ , _, _, _, _, Hmrs, _, _, _, _, _, _, (_ & Hneq_blk & _)).
    unfold match_regions in *.
    rewrite <- upd_pc_same_mrs.
    rewrite <- upd_pc_same_mrs_num.
    destruct Hmrs as (Hload & Hmrs_len & Hmrs_ge & Hmrs).

    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).

    split; [assumption| ].
    split; [assumption| ].
    eapply upd_preserves_match_list_region; eauto.
    intro HF.
    rewrite NoDup_cons_iff in Hneq_blk.
    apply Hneq_blk.
    rewrite HF.
    left; reflexivity.
  - 
    destruct Hst' as (_ , _, _, _, _, _, (Hins_len & Hge), _, _, _, _, _, _).
    rewrite <- upd_pc_same_ins_len.
    split; [| assumption].
    rewrite <- Hins_len.
    simpl.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
  -
    destruct Hst' as (_ , _, _, _, _, _, _, Hins, _, _, _, _, (_ & Hneq_blk & _)).
    unfold match_ins in *.
    destruct Hins as (Hload & Hins_len & Hins_max & Hins).
    rewrite <- upd_pc_same_ins.
    rewrite <- upd_pc_same_ins_len.
    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).

    split; [assumption |].
    split; [assumption |].
    eapply upd_preserves_match_list_ins; eauto.
    intro HF.
    rewrite NoDup_cons_iff in Hneq_blk.
    apply Hneq_blk.
    rewrite HF. right.
    left; reflexivity.
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, Hins, _, _, _, (_ & Hneq_blk & _)).
    unfold match_kv in *.
    destruct Hins as (Hload & Hins_len & Hins_max & Hins).
    rewrite <- upd_pc_same_ins_len.
    rewrite <- upd_pc_same_tp_kv.

    split.
    { rewrite <- Hload.
      eapply Mem.load_store_other; eauto.
      right; right.
      rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    }

    split; [assumption |].
    split; [assumption |].
    eapply upd_preserves_match_list_kv; eauto.
    intro HF.
    rewrite NoDup_cons_iff in Hneq_blk.
    apply Hneq_blk.
    rewrite HF. right. right.
    left; reflexivity.
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, _,(Hins_len & Hge), _, _, _).
    rewrite <- upd_pc_same_tp_bin_len.
    split; [| assumption].
    rewrite <- Hins_len.
    simpl.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, _, _, Hins, _, (_ & Hneq_blk & _)).
    unfold match_jit in *.
    destruct Hins as (Hload & (Hins_len & Hins_max & Hins) & Hblk1 & Hblk2).
    rewrite <- upd_pc_same_ins.
    rewrite <- upd_pc_same_tp_bin_len.
    rewrite <- upd_pc_same_tp_bin.

    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).

    split.
    split; [assumption |].
    split; [assumption |].
    eapply upd_preserves_match_list_jit; eauto.
    intro HF.
    rewrite NoDup_cons_iff in Hneq_blk.
    apply Hneq_blk.
    rewrite HF. right. right; right.
    left; reflexivity.

    split; assumption.
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, _, _, _, Hperm, _).
    rewrite <- upd_pc_same_mrs_num.
    unfold Mem.range_perm in *.
    destruct Hperm as (Hperm0 & Hperm1 & Hperm2 & Hperm3 & Hperm4).
    split; [ intros | ].
    { eapply Mem.perm_store_1; eauto. }
    split; [ intros | ].
    { eapply Mem.perm_store_1; eauto. }
    split; [ intros | ].
    { eapply Mem.perm_store_1; eauto. }
    split; [ intros | ].
    { eapply Mem.perm_store_1; eauto. }
    intros.
    { eapply Mem.perm_store_1; eauto. }
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, _, _, _, _, Hvalid).
    rewrite <- upd_pc_same_mem.
    intuition.
    apply H3; auto.
    eapply Mem.store_valid_block_2; eauto.
Qed.

Lemma upd_flag_preserves_match_state:
  forall st0 st1 m0 m1 {S: special_blocks} flag
  (Hst    : match_state  st0 m0)
  (Hst1   : upd_flag flag st0 = st1)
  (Hstore : Mem.store AST.Mint32 m0 st_blk 48 (Vint (int_of_flag flag)) = Some m1),
    match_state  st1 m1.
Proof.
  intros.
  subst.
  set (Hst' := Hst).
  split.
  -
    destruct Hst' as (Hunchanged_on, _, _, _, _, _, _, _, _, _, _, _, _).
    rewrite <- upd_flag_same_mem.
    assert (Hunchanged_on': Mem.unchanged_on (fun (b : block) (_ : Z) =>
      b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk /\ b <> jit_blk /\ b <> kv_blk) m0 m1). {
      eapply Mem.store_unchanged_on; eauto.
      intros.
      intro H0; destruct H0 as (H0 & _); apply H0; reflexivity.
    }
    apply Mem.unchanged_on_trans with(m2:= m0); auto.
  -
    destruct Hst' as (_ , Hregs, _, _, _, _, _, _, _, _, _, _, _).
    rewrite <- upd_flag_same_regs.
    unfold match_registers in *.
    intros.
    specialize (Hregs r).
    destruct Hregs as (vl & Hload & Hvl_eq).
    exists vl.
    split; [| assumption].
    rewrite <- Hload.
    unfold Mem.loadv.
    eapply Mem.load_store_other.
    apply Hstore.
    right; left.
    unfold Ptrofs.add in *.
    unfold size_chunk.
    rewrite Ptrofs_unsigned_repr_id_of_reg in *. unfold id_of_reg; destruct r; lia.
  -
    destruct Hst' as (_ , _, Hpc, _, _, _, _, _, _, _, _, _, _).
    rewrite <- upd_flag_same_pc.
    rewrite <- Hpc.
    eapply Mem.load_store_other.
    apply Hstore.
    right; left.
    reflexivity.
  -
    destruct Hst' as (_ , _, Hflag, _, _, _, _, _, _, _, _, _, _).

    unfold Mem.loadv in *.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
    apply Mem.load_store_same in Hstore.
    rewrite Hstore.
    unfold Val.load_result.
    reflexivity.
  -
    destruct Hst' as (_ , _, _, _, (Hmrs_len & Hge), _, _, _, _, _, _, _, _).
    rewrite <- upd_flag_same_mrs_num.
    split; [| assumption].
    rewrite <- Hmrs_len.
    simpl.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
  - 
    destruct Hst' as (_ , _, _, _, _, Hmrs, _, _, _, _, _, _, (_ & Hneq_blk & _)).
    unfold match_regions in *.
    rewrite <- upd_flag_same_mrs.
    rewrite <- upd_flag_same_mrs_num.
    destruct Hmrs as (Hload & Hmrs_len & Hmrs_ge & Hmrs).

    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).

    split; [assumption| ].
    split; [assumption| ].
    eapply upd_preserves_match_list_region; eauto.
    intro HF.
    rewrite NoDup_cons_iff in Hneq_blk.
    apply Hneq_blk.
    rewrite HF.
    left; reflexivity.
  -
    destruct Hst' as (_ , _, _, _, _, _, (Hins_len & Hge), _, _, _, _, _, _).
    rewrite <- upd_flag_same_ins_len.
    split; [| assumption].
    rewrite <- Hins_len.
    simpl.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
  - 
    destruct Hst' as (_ , _, _, _, _, _, _, Hins, _, _, _, _, (_ & Hneq_blk & _)).
    unfold match_ins in *.
    destruct Hins as (Hload & Hins_len & Hins_max & Hins).
    rewrite <- upd_flag_same_ins.
    rewrite <- upd_flag_same_ins_len.

    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).

    split; [assumption |].
    split; [assumption |].
    eapply upd_preserves_match_list_ins; eauto.
    intro HF.
    rewrite NoDup_cons_iff in Hneq_blk.
    apply Hneq_blk.
    rewrite HF. right.
    left; reflexivity.
  - 
    destruct Hst' as (_ , _, _, _, _, _, _, _, Hins, _, _, _, (_ & Hneq_blk & _)).
    unfold match_kv in *.
    destruct Hins as (Hload & Hins_len & Hins_max & Hins).
    rewrite <- upd_flag_same_ins_len.
    rewrite <- upd_flag_same_tp_kv.

    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).

    split; [assumption |].
    split; [assumption |].
    eapply upd_preserves_match_list_kv; eauto.
    intro HF.
    rewrite NoDup_cons_iff in Hneq_blk.
    apply Hneq_blk.
    rewrite HF. right. right.
    left; reflexivity.
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, _, (Hins_len & Hge), _, _, _).
    rewrite <- upd_flag_same_tp_bin_len.
    split; [| assumption].
    rewrite <- Hins_len.
    simpl.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, _, _, Hins, _, (_ & Hneq_blk & _)).
    unfold match_jit in *.
    destruct Hins as (Hload & (Hins_len & Hins_max & Hins) & Hblk1 & Hblk2).
    rewrite <- upd_flag_same_ins.
    rewrite <- upd_flag_same_tp_bin_len.
    rewrite <- upd_flag_same_tp_bin.

    split.
    rewrite <- Hload.
    eapply Mem.load_store_other; eauto.
    right; right.
    rewrite Ptrofs_unsigned_repr_n in *; try (simpl; lia).

    split; [| split; assumption].
    split; [assumption |].
    split; [assumption |].
    eapply upd_preserves_match_list_jit; eauto.
    intro HF.
    rewrite NoDup_cons_iff in Hneq_blk.
    apply Hneq_blk.
    rewrite HF. right. right; right.
    left; reflexivity.
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, _, _, _, Hperm, _).
    rewrite <- upd_flag_same_mrs_num.
    unfold Mem.range_perm in *.
    destruct Hperm as (Hperm0 & Hperm1 & Hperm2 & Hperm3 & Hperm4).
    repeat (split; [ intros; eapply Mem.perm_store_1; eauto |]).
    intros; eapply Mem.perm_store_1; eauto.
  -
    destruct Hst' as (_ , _, _, _, _, _, _, _, _, _, _, _, Hvalid).
    rewrite <- upd_flag_same_mem.
    intuition.
    apply H3; auto.
    eapply Mem.store_valid_block_2; eauto.
Qed.

Lemma match_state_implies_valid_pointer:
  forall  {S:special_blocks} st m b ofs
    (Hmatch : match_state  st m)
    (Hvalid : Mem.valid_pointer (bpf_m st) b ofs = true),
      Mem.valid_pointer m b ofs = true.
Proof.
  intros.
  rewrite Mem.valid_pointer_nonempty_perm in *.
  destruct Hmatch.
  eapply Mem.perm_unchanged_on; eauto.
  simpl.
  apply Mem.perm_valid_block in Hvalid.
  clear - minvalid0 Hvalid.
  destruct minvalid0 as ((Hv0 & Hv1 & Hv2 & Hv3 & Hv4) & HNoDup & H).
  repeat split.
  all: eapply Mem.valid_not_valid_diff; eauto.
Qed.

Lemma match_state_implies_loadv_equal:
  forall {S: special_blocks} st m chunk b ofs v
    (Hmatch : match_state st m)
    (Hload: Mem.load chunk (bpf_m st) b ofs = Some v),
      Mem.load chunk m b ofs = Some v.
Proof.
  intros.
  set (Hmatch' := Hmatch).
  destruct Hmatch' as (Hunchanged, _, _, _, _, _, _, _, _, _, _, _, Hinvalid).
  rewrite <- Hload.
  destruct Hinvalid as (Hinvalid & _ & Hvalid_block).
  apply Mem.load_valid_access in Hload.
  assert (Hload' : Mem.valid_access (bpf_m st) chunk b ofs Nonempty). {
    eapply Mem.valid_access_implies; eauto.
    constructor.
  }
  eapply Mem.valid_access_valid_block in Hload'; eauto.
  eapply Mem.load_unchanged_on_1; eauto.
  simpl; intros.
  intuition congruence.
Qed.

Lemma store_reg_preserive_match_state:
  forall {S:special_blocks} st1 st2 m1 chunk b ofs addr m
    (Hst: match_state  st1 m1)
    (Hstore: Mem.store chunk (bpf_m st1) b ofs addr = Some m)
    (Hupd_st: upd_mem m st1 = st2),
      exists m2,
        Mem.store chunk m1 b ofs addr = Some m2 /\
        match_state  st2 m2.
Proof.
  intros.
  assert (Hvalid_blk': Mem.valid_block (bpf_m st1) b). {
    destruct Hst as (Hunchanged_on, _, _, _, _, _, _, _, _, _, _, _, _).
    apply Mem.store_valid_access_3 in Hstore.
    assert (Hstore' : Mem.valid_access (bpf_m st1) chunk b ofs Nonempty). {
      eapply Mem.valid_access_implies; eauto.
      constructor.
    }
    eapply Mem.valid_access_valid_block in Hstore'; eauto.
  }
  assert (Hvalid_blk: Mem.valid_block m1 b). {
    destruct Hst as (Hunchanged_on, _, _, _, _, _, _, _, _, _, _, _, _).
    eapply Mem.valid_block_unchanged_on; eauto.
  }

  assert (Hinvalid: b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk /\ b <> jit_blk /\ b <> kv_blk). {
    destruct Hst as (_, _, _, _, _, _, _, _, _, _, _, _, Hinvalid).
    destruct Hinvalid as ((Hinvalid0 & Hinvalid1 & Hinvalid2 & Hinvalid3 & Hinvalid4) & _ & _).
    split.
    intro; subst.
    apply Hinvalid0; assumption.
    split. intro HF; subst.
    apply Hinvalid1; auto.
    split. intro HF; subst.
    apply Hinvalid2; auto.
    split; intro; subst.
    apply Hinvalid4; assumption.
    apply Hinvalid3; assumption.
  }

  assert (Hvalid_access: Mem.valid_access m1 chunk b ofs Writable). {
    destruct Hst.
    destruct minvalid0 as ( _ & _ & Hvalid).
    specialize (Hvalid b Hinvalid Hvalid_blk).
    clear - munchange0 Hvalid Hvalid_blk Hinvalid Hstore.
    destruct munchange0.

    eapply Mem.store_valid_access_3 in Hstore as Hvalid_acc; eauto.
    eapply Mem.valid_access_store with (v:= addr) in Hvalid_acc as Hres; eauto.

    unfold Mem.valid_access in *.
    destruct Hvalid_acc as (Hvalid_acc & Haligh).
    split; [| assumption].
    unfold Mem.range_perm in *.
    intros.
    specialize (Hvalid_acc ofs0 H).
    specialize (unchanged_on_perm b ofs0 Cur Writable Hinvalid Hvalid).
    apply unchanged_on_perm; assumption.
  }
  eapply Mem.valid_access_store with (v:= addr) in Hvalid_access; eauto.
  destruct Hvalid_access as (m2 & Hstore_m2).
  exists m2.
  split; [assumption |].

  subst.
  set (Hst' := Hst).
  split.
  - (**r Mem.unchanged_on *)
    destruct Hst' as (Hunchanged_on, _, _, _, _, _, _, _, _, _, _, _, _).
    destruct Hunchanged_on.
    unfold upd_mem; simpl.
    split.
    + eapply Mem.nextblock_store in Hstore_m2; auto.
      rewrite Hstore_m2.
      eapply Mem.nextblock_store in Hstore; auto.
      rewrite Hstore.
      assumption.
    + intros.
      eapply Mem.store_valid_block_2 in Hstore as Hvalid_block; eauto.
      specialize (unchanged_on_perm b0 ofs0 k p H Hvalid_block).
      eapply store_perm_iff with (b0:=b0) (ofs0:=ofs0) (k:=k) (p:=p) in Hstore as Hperm_1; eauto.
      eapply store_perm_iff with (b0:=b0) (ofs0:=ofs0) (k:=k) (p:=p) in Hstore_m2 as Hperm_2; eauto.
      intuition.
    + intros.
      eapply Mem.perm_store_2 in Hstore as Hperm; eauto.
      specialize (unchanged_on_contents b0 ofs0 H Hperm).
      clear unchanged_on_nextblock unchanged_on_perm H0 Hperm.

      destruct (b0 =? b)%positive eqn: Hblk_eq; [rewrite Pos.eqb_eq in Hblk_eq | rewrite Pos.eqb_neq in Hblk_eq].
      * (**r b0 = b *)
        subst.
        destruct (ofs0 =? ofs)%Z eqn: Hofs_eq; [rewrite Z.eqb_eq in Hofs_eq | rewrite Z.eqb_neq in Hofs_eq].
        ** (**r ofs0 = ofs *)
          subst.
          eapply store_store_same_block; eauto.
        ** (**r ofs0 <> ofs *)
          rewrite Z.lt_gt_cases in Hofs_eq.
          destruct Hofs_eq as [Hofs_le | Hofs_ge].
          { (**r ofs0 < ofs*)
            eapply store_store_other_block_same; eauto.
          }
          { (**r ofs < ofs0 *)
            destruct (ofs + size_chunk chunk <=? ofs0)%Z eqn: Hge; [rewrite Z.leb_le in Hge | rewrite Z.leb_gt in Hge].
            { (**r ofs + size_chunk chunk <= ofs0 *)
              eapply store_store_other_block_same; eauto.
            }
            { (**r ofs < ofs0 < ofs + size_chunk chunk *)
              eapply store_store_same_block_other; eauto.
            }
          }
      * (**r b0 <> b *)
        eapply store_store_other_block_same; eauto.
  - (**r registers *)
    destruct Hst' as (_, Hreg, _, _, _, _, _, _, _, _, _, _, _).
    unfold match_registers in *.
    intros.
    specialize (Hreg r).
    destruct Hreg as (vl & Hload & Hvl_eq).
    unfold Mem.loadv in *.
    unfold upd_mem; simpl regs_st.
    exists vl.
    split; [| assumption].
    eapply Mem.load_store_other in Hstore_m2.
    rewrite Hstore_m2.
    assumption.
    intuition.
  - (**r pc *)
    destruct Hst' as (_, _, Hpc, _, _, _, _, _, _, _, _, _, _).
    unfold Mem.loadv in *.
    unfold upd_mem; simpl.
    eapply Mem.load_store_other in Hstore_m2.
    rewrite Hstore_m2.
    assumption.
    intuition.
  - (**r flag *)
    destruct Hst' as (_, _, _, Hflag, _, _, _, _, _, _, _, _, _).
    unfold Mem.loadv in *.
    unfold upd_mem; simpl.
    eapply Mem.load_store_other in Hstore_m2.
    rewrite Hstore_m2.
    assumption.
    intuition.
  - (**r mrs_num *)
    destruct Hst' as (_, _, _, _, Hmrs_num, _, _, _, _, _, _, _, _).
    unfold Mem.loadv in *.
    destruct Hmrs_num as (Hload & Hother).
    unfold upd_mem; simpl.
    split.

    eapply Mem.load_store_other in Hstore_m2.
    rewrite Hstore_m2.
    assumption.
    intuition.

    assumption.
  - (**r mrs_block *)
    destruct Hst' as (_, _, _, _, _, Hmrs_block, _, _, _, _, _, _, _).
    unfold Mem.loadv in *.
    unfold match_regions in *.
    unfold upd_mem; simpl.
    destruct Hmrs_block as (Hload & Hlen & Hmax & Hmatch).
    split.

    eapply Mem.load_store_other in Hstore_m2.
    rewrite Hstore_m2.
    assumption.
    intuition.

    split; [assumption| ].
    split; [assumption| ].
    eapply upd_preserves_match_list_region; eauto.
    intuition.
  - (**r ins_len *)
    destruct Hst' as (_, _, _, _, _, _, Hins_len, _, _, _, _, _, _).
    unfold Mem.loadv in *.
    unfold upd_mem; simpl.
    destruct Hins_len as (Hload & Hge).
    split; [| assumption].
    eapply Mem.load_store_other in Hstore_m2.
    rewrite Hstore_m2.
    assumption.
    intuition.
  - (**r ins *)
    destruct Hst' as (_, _, _, _, _, _, _, Hins, _, _, _, _, _).
    unfold Mem.loadv in *.
    unfold match_ins in *.
    destruct Hins as (Hload & Hlen & Hmax & Hmatch).
    unfold upd_mem; simpl.
    split.

    eapply Mem.load_store_other in Hstore_m2.
    rewrite Hstore_m2.
    assumption.
    intuition.

    split; [assumption| ].
    split; [assumption| ].
    eapply upd_preserves_match_list_ins; eauto.
    intuition.
  - (**r tp_kv *)
    destruct Hst' as (_, _, _, _, _, _, _, _, Hins, _, _, _, _).
    unfold Mem.loadv in *.
    unfold match_kv in *.
    destruct Hins as (Hload & Hlen & Hmax & Hmatch).
    unfold upd_mem; simpl.
    split.

    eapply Mem.load_store_other in Hstore_m2.
    rewrite Hstore_m2.
    assumption.
    intuition.

    split; [assumption| ].
    split; [assumption| ].
    eapply upd_preserves_match_list_kv; eauto.
    intuition.
  - (**r tp_bin_len *)
    destruct Hst' as (_, _, _, _, _, _, _, _, _, Hins_len, _, _, _).
    unfold Mem.loadv in *.
    unfold upd_mem; simpl.
    destruct Hins_len as (Hload & Hge).
    split; [| assumption].
    eapply Mem.load_store_other in Hstore_m2.
    rewrite Hstore_m2.
    assumption.
    intuition.
  - (**r tp_bin *)
    destruct Hst' as (_, _, _, _, _, _, _, _, _, _, Hins, _, _).
    unfold Mem.loadv in *.
    unfold match_jit in *.
    destruct Hins as (Hload & (Hlen & Hmax & Hmatch) & Hblk1 & Hblk2).
    unfold upd_mem; simpl.
    split.

    eapply Mem.load_store_other in Hstore_m2.
    rewrite Hstore_m2.
    assumption.
    intuition.

    split; [| split; assumption].
    split; [assumption| ].
    split; [assumption| ].
    eapply upd_preserves_match_list_jit; eauto.
    intuition.
  - (**r range_perm *)
    destruct Hst' as (_, _, _, _, _, _, _, _, _, _, _, Hrange_perm, _).
    unfold upd_mem.
    simpl mrs_num.
    simpl input_len.
    destruct Hrange_perm as (Hrange_perm_st & Hrange_perm_mrs & Hrange_perm_ins).
    repeat (split; [eapply store_range_perm; eauto; intuition |]).
    eapply store_range_perm; eauto; intuition.
  - (**r valid_block *)
    destruct Hst' as (_, _, _, _, _, _, _, _, _, _, _, _, Hvalid_block).
    unfold upd_mem; simpl.
    destruct Hvalid_block as (Hinvalid_blk & Hneq_blk & Hvalid).
    destruct Hinvalid_blk as (Hinvalid_blk0 & Hinvalid_blk1 & Hinvalid_blk2 & Hinvalid_blk3 & Hinvalid_blk4).
    split.
    split.
    intro H; apply Hinvalid_blk0; eapply Mem.store_valid_block_2; eauto.
    split.
    intro H; apply Hinvalid_blk1; eapply Mem.store_valid_block_2; eauto.
    split.
    intro H; apply Hinvalid_blk2; eapply Mem.store_valid_block_2; eauto.
    split.
    intro H; apply Hinvalid_blk3; eapply Mem.store_valid_block_2; eauto.
    intro H; apply Hinvalid_blk4; eapply Mem.store_valid_block_2; eauto.
    split; [assumption | ].
    intros.
    specialize (Hvalid b0 H).
    eapply Mem.store_valid_block_2 in Hstore_m2; eauto.
    specialize (Hvalid Hstore_m2).
    eapply Mem.store_valid_block_1 in Hstore; eauto.
Qed.

Close Scope Z_scope.

#[global] Notation dcons := (DList.DCons (F:= fun x => x -> Inv hybrid_state)).
