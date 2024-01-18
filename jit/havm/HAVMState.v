From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values Memory AST.
From compcert.lib Require Import Integers.
From compcert.arm Require Import ABinSem.

From bpf.comm Require Import ListAsArray Flag Regs MemRegion rBPFAST rBPFValues JITCall.
From bpf.jit Require Import KeyValue2.

From Coq Require Import List ZArith.
Import ListNotations.

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

Definition init_mem: mem := Mem.empty.

Definition init_state: hybrid_state := {|
  regs_st     := init_regmap;
  pc_loc      := Int.zero;
  flag        := BPF_OK;
  mrs_num     := 0;
  bpf_mrs     := default_memory_regions;
  input_len   := 0;
  input_ins   := [];
  tp_kv       := [];
  tp_bin_len  := 0;
  tp_bin      := [];
  bpf_m   := init_mem;
 |}.

Definition check_pc (st: hybrid_state): bool :=
  Int.cmpu Clt (pc_loc st) (Int.repr (Z.of_nat (input_len st))).

Definition check_pc_incr (st: hybrid_state): bool :=
  Int.cmpu Clt (Int.add (pc_loc st) Int.one) (Int.repr (Z.of_nat (input_len st))).

Definition upd_pc (p: int) (st:hybrid_state): hybrid_state := {|
  regs_st     := regs_st st;
  pc_loc      := Int.add (pc_loc st) p;
  flag        := flag st;
  mrs_num     := mrs_num st;
  bpf_mrs     := bpf_mrs st;
  input_len   := input_len st;
  input_ins   := input_ins st;
  tp_kv       := tp_kv st;
  tp_bin_len  := tp_bin_len st;
  tp_bin      := tp_bin st;
  bpf_m       := bpf_m st;
|}.

Definition eval_flag (st:hybrid_state): bpf_flag := flag st.

Definition upd_flag (f: bpf_flag) (st:hybrid_state): hybrid_state := {|
  regs_st     := regs_st st;
  pc_loc      := pc_loc st;
  flag        := f;
  mrs_num     := mrs_num st;
  bpf_mrs     := bpf_mrs st;
  input_len   := input_len st;
  input_ins   := input_ins st;
  tp_kv       := tp_kv st;
  tp_bin_len  := tp_bin_len st;
  tp_bin      := tp_bin st;
  bpf_m       := bpf_m st;
|}.

Definition upd_regs (rs: regmap) (st:hybrid_state): hybrid_state := {|
  regs_st     := rs;
  pc_loc      := pc_loc st;
  flag        := flag st;
  mrs_num     := mrs_num st;
  bpf_mrs     := bpf_mrs st;
  input_len   := input_len st;
  input_ins   := input_ins st;
  tp_kv       := tp_kv st;
  tp_bin_len  := tp_bin_len st;
  tp_bin      := tp_bin st;
  bpf_m       := bpf_m st;
|}.

Definition eval_reg (r: reg) (st:hybrid_state): val :=
  eval_regmap r (regs_st st).

Definition upd_reg (r:reg) (v:val) (st:hybrid_state): hybrid_state := {|
  regs_st     := upd_regmap r v (regs_st st);
  pc_loc      := pc_loc st;
  flag        := flag st;
  mrs_num     := mrs_num st;
  bpf_mrs     := bpf_mrs st;
  input_len   := input_len st;
  input_ins   := input_ins st;
  tp_kv       := tp_kv st;
  tp_bin_len  := tp_bin_len st;
  tp_bin      := tp_bin st;
  bpf_m       := bpf_m st;
|}.

Definition eval_mem_num (st:hybrid_state): nat := (mrs_num st). (**r uint32_t -> nat*)

Definition eval_mem_regions (st:hybrid_state): MyMemRegionsType := bpf_mrs st.

Definition eval_mem (st: hybrid_state):Mem.mem := bpf_m st.

Definition upd_mem (m: Mem.mem) (st: hybrid_state): hybrid_state := {| (**r never be used I guess *)
  regs_st     := regs_st st;
  pc_loc      := pc_loc st;
  flag        := flag st;
  mrs_num     := mrs_num st;
  bpf_mrs     := bpf_mrs st;
  input_len   := input_len st;
  input_ins   := input_ins st;
  tp_kv       := tp_kv st;
  tp_bin_len  := tp_bin_len st;
  tp_bin      := tp_bin st;
  bpf_m       := m;
|}.

Definition load_mem (chunk: memory_chunk) (ptr: val) (st: hybrid_state): option val :=
  match chunk with
  | Mint8unsigned | Mint16unsigned | Mint32 =>
    match Mem.loadv chunk (bpf_m st) ptr with
    | Some res =>
      match res with
      | Vint v => Some (Vint v)
      | _ => None
      end
    | None => None
    end
  | _ => None
  end
.

Definition store_mem (ptr: val) (chunk: memory_chunk) (v: val) (st: hybrid_state): option hybrid_state :=
  match chunk with
  | Mint8unsigned | Mint16unsigned | Mint32 =>
    let src := vint_to_vint chunk v in
      match Mem.storev chunk (bpf_m st) ptr src with
      | Some m => Some (upd_mem m st)
      | None => None
      end
  | _ => None
  end
.

Definition eval_ins_len (st: hybrid_state): int := Int.repr (Z.of_nat (input_len st)).
Definition eval_ins (st: hybrid_state): option int64 := List64AsArray.index (input_ins st) (Z.to_nat (Int.unsigned (pc_loc st))).



(** @input
  * @fuel : the size of selected jitted_arm list because of no-loop
  * @ofs  : the location of the selected jitted_arm part in the whole jitted_arm array
  * @sz   : the stack_size allocated accroding to the selected jitted_arm part
  * @st   : the initial jit state

  * @output
  * the updated jit state and
  *)
Definition jit_call (st: hybrid_state): option hybrid_state :=
  match ListKeyV.index (tp_kv st) (Z.to_nat (Int.unsigned (pc_loc st))) with
  | None => None
  | Some v =>
    match jit_call_simpl (arm_ofs v) (pc_loc st) (regs_st st) (bpf_m st) with
    | None => None
    | Some (pc', rs', m') =>
      let st1 := upd_pc pc' st in
      let st2 := upd_regs rs' st1 in
        Some (upd_mem m' st2)
    end
  end.

