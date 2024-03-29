From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Import Values Memory AST.
From compcert.lib Require Import Integers.
From compcert.arm Require Import ABinSem.

From bpf.comm Require Import ListAsArray Flag MemRegion rBPFAST rBPFValues JITCall.

From bpf.rbpf32 Require Import TSSyntax JITConfig.

From Coq Require Import List ZArith.
Import ListNotations.

Definition get_mem_region (n mrs_num: nat) (mrs: MyMemRegionsType): option memory_region :=
  if (Nat.ltb n mrs_num) then
    match List.nth_error mrs n with
    | Some mr => Some mr
    | None => None
    end
  else
    None.


Record state := mkst {
  flag    : bpf_flag;
  regs_st : regset;
  mrs_num : nat;
  bpf_mrs : MyMemRegionsType;
  ins_len : nat;
  ins     : List64AsArray.t;
  tp_kv   : ListNat.t;
  tp_bin  : List32.t;
  bpf_m   : Memory.mem;
}.

Definition eval_cmp (cop: cmpOp) (d: breg) (s: breg+imm) (st:state): option bool :=
  eval_cmp cop (regs_st st) (bpf_m st) d s.

Definition init_mem: mem := Mem.empty.

Definition init_state: state := {|
  flag    := BPF_OK;
  regs_st := (BPregmap.init Vzero);
  mrs_num := 0;
  bpf_mrs := default_memory_regions;
  ins_len := 0;
  ins     := [];
  tp_kv   := [];
  tp_bin  := [];
  bpf_m   := init_mem;
 |}.

Definition upd_pc (p: val) (st:state): state := {|
  flag    := flag st;
  regs_st := (regs_st st)#BPC <- (Val.add (regs_st st)#BPC p);
  mrs_num := mrs_num st;
  bpf_mrs := bpf_mrs st;
  ins_len := ins_len st;
  ins     := ins st;
  tp_kv   := tp_kv st;
  tp_bin  := tp_bin  st;
  bpf_m   := bpf_m st;
|}.

Definition eval_flag (st:state): bpf_flag := flag st.

Definition upd_flag (f: bpf_flag) (st:state): state := {|
  flag    := f;
  regs_st := regs_st st;
  mrs_num := mrs_num st;
  bpf_mrs := bpf_mrs st;
  ins_len := ins_len st;
  ins     := ins st;
  tp_kv   := tp_kv st;
  tp_bin  := tp_bin  st;
  bpf_m   := bpf_m st;
|}.


Definition upd_regs (rs: regset) (st:state): state := {|
  flag    := flag st;
  regs_st := rs;
  mrs_num := mrs_num st;
  bpf_mrs := bpf_mrs st;
  ins_len := ins_len st;
  ins     := ins st;
  tp_kv   := tp_kv st;
  tp_bin  := tp_bin  st;
  bpf_m   := bpf_m st;
|}.

Definition eval_reg (r: breg) (st:state): val :=
  (regs_st st)#r.

Definition upd_reg (r: breg) (v:val) (st:state): state := {|
  flag    := flag st;
  regs_st := (regs_st st)#r <- v;
  mrs_num := mrs_num st;
  bpf_mrs := bpf_mrs st;
  ins_len := ins_len st;
  ins     := ins st;
  tp_kv   := tp_kv st;
  tp_bin  := tp_bin  st;
  bpf_m   := bpf_m st;
|}.

Definition eval_mem_num (st:state): nat := (mrs_num st). (**r uint32_t -> nat*)

Definition eval_mem_regions (st:state): MyMemRegionsType := bpf_mrs st.

Definition eval_mem (st: state):Mem.mem := bpf_m st.

Definition upd_mem (m: Mem.mem) (st: state): state := {| (**r never be used I guess *)
  flag    := flag st;
  regs_st := regs_st st;
  mrs_num := mrs_num st;
  bpf_mrs := bpf_mrs st;
  ins_len := ins_len st;
  ins     := ins st;
  tp_kv   := tp_kv st;
  tp_bin  := tp_bin  st;
  bpf_m   := m;
|}.

Definition load_mem (chunk: memory_chunk) (ptr: val) (st: state): option val :=
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

Definition store_mem (ptr: val) (chunk: memory_chunk) (v: val) (st: state): option state :=
  match chunk with
  | Mint8unsigned | Mint16unsigned | Mint32 =>
      match Mem.storev chunk (bpf_m st) ptr v with
      | Some m => Some (upd_mem m st)
      | None => None
      end
  | _ => None
  end
.

Definition eval_ins_len (st: state): int := Int.repr (Z.of_nat (ins_len st)).
Definition eval_ins (st: state): option int64 :=
  match (regs_st st)#BPC with
  | Vint i => 
    if (Int.cmpu Clt i (Int.repr (Z.of_nat (ins_len st)))) then
      List64AsArray.index (ins st) (Z.to_nat (Int.unsigned i))
    else
      None
  | _ => None
  end.

Definition cmp_ptr32_nullM (v: val) (st: state): option bool := cmp_ptr32_null (bpf_m st) v.

Definition jit_call_simplb (kv: list nat) (rs: regset) (m: mem): option (regset * mem) :=
  let fuel  := JITTED_LIST_MAX_LENGTH in
  let sz    := (Int.repr stack_block_size) in (**r 12 * 4 *)
  match rs#BPC with
  | Vint pc =>
    match ListNat.index kv (Z.to_nat (Int.unsigned pc)) with
    | None => None
    | Some ofs =>
      let (m1, st_blk) := Mem.alloc m 0 state_block_size in
        match copy_to rs st_blk m1 with
        | None => None
        | Some m2 =>
          let arm_argu_list_val :=
            [ (Vptr jit_arm_block (Ptrofs.of_intu (Int.repr (Z.of_nat (4* ofs)))));
              (Vptr st_blk Ptrofs.zero)] in
            match bin_exec fuel compcertbin_signature (Int.unsigned sz)
              Ptrofs.zero arm_argu_list_val m2 with
            | None => None
            | Some (_, m3) =>
              match copy_from rs st_blk m3 with
              | None => None
              | Some rs' => Some (rs', m)
              end
            end
        end
    end
  | _ => None
  end.

Axiom _bpf_get_call : ident -> signature -> mem -> option (val * mem).