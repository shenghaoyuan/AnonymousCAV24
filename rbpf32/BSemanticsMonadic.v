From compcert Require Import Memory Memtype Integers Values Ctypes AST.
From Coq Require Import ZArith Lia.

From bpf.comm Require Import Flag rBPFValues Regs BinrBPF Monad MemRegion rBPFAST rBPFMemType.
From bpf.rbpf32 Require Import TSSyntax TSDecode BState BStateMonadOp.

Open Scope monad_scope.

Definition get_add (x y: val): M val := returnM (Val.add x y).

Definition get_sub (x y: val): M val := returnM (Val.sub x y).

Definition get_addr_ofs (x: val) (ofs: int): M val := returnM ((Val.add x (sint32_to_vint ofs))).

Definition get_start_addr (mr: memory_region): M val := returnM (start_addr mr).

Definition get_block_size (mr: memory_region): M val := returnM (block_size mr).

Definition get_block_perm (mr: memory_region): M permission := returnM (block_perm mr).

Definition check_mem_aux2 (mr: memory_region) (perm: permission) (addr: val) (chunk: memory_chunk): M val :=
  do start  <- get_start_addr mr;
  do size   <- get_block_size mr;
  do mr_perm  <- get_block_perm mr;
  do lo_ofs <- get_sub addr start;
  do hi_ofs <- get_add lo_ofs (memory_chunk_to_valu32 chunk);
    if andb (andb
              (compu_le hi_ofs size)
              (andb (compu_le lo_ofs (memory_chunk_to_valu32_upbound chunk))
                    (comp_eq Vzero (val32_modu lo_ofs (memory_chunk_to_valu32 chunk)))))
            (perm_ge mr_perm perm) then
            returnM (Val.add (block_ptr mr) lo_ofs) (**r Vptr b lo_ofs *)
    else
      returnM Vnullptr.

Fixpoint check_mem_aux (num: nat) (perm: permission) (chunk: memory_chunk) (addr: val) (mrs: MyMemRegionsType)  {struct num}: M val :=
  match num with
  | O => returnM Vnullptr
  | S n =>
    do cur_mr     <- get_mem_region n mrs;
    do check_ptr  <- check_mem_aux2 cur_mr perm addr chunk;
    do is_null    <- cmp_ptr32_nullM check_ptr;
      if is_null then
        check_mem_aux n perm chunk addr mrs
      else
        returnM check_ptr
  end.

Definition check_mem (perm: permission) (chunk: memory_chunk) (addr: val): M val :=
      do mem_reg_num  <- eval_mem_num;
      do mrs          <- eval_mem_regions;
      do check_ptr    <- check_mem_aux mem_reg_num perm chunk addr mrs;
      do is_null      <- cmp_ptr32_nullM check_ptr;
        if is_null then
          returnM Vnullptr
        else
          returnM check_ptr.

Definition step_load_x_operation (chunk: memory_chunk) (d:breg) (s:breg) (ofs:off): M unit :=
  do mrs  <- eval_mem_regions;
  do sv   <- eval_reg s;
  do addr <- get_addr_ofs sv ofs;
  do ptr  <- check_mem Readable chunk addr;
  do is_null   <- cmp_ptr32_nullM ptr;
    if is_null then
      upd_flag BPF_ILLEGAL_MEM
    else
      do v <- load_mem chunk ptr;
      do _ <- upd_reg d v; returnM tt
.

Definition step_store_operation (chunk: memory_chunk) (d: breg) (s: breg+imm) (ofs: off): M unit :=
  do mrs  <- eval_mem_regions;
  do dv   <- eval_reg d;
  do addr <- get_addr_ofs dv ofs;

    match s with
    | inl r =>
      do src <- eval_reg r;
      do ptr  <- check_mem Writable chunk addr;
      do is_null   <- cmp_ptr32_nullM ptr;
        if is_null then
          upd_flag BPF_ILLEGAL_MEM
        else
          do _ <- store_mem ptr chunk src; returnM tt
    | inr i =>
      do ptr  <- check_mem Writable chunk addr;
      do is_null   <- cmp_ptr32_nullM ptr;
        if is_null then
          upd_flag BPF_ILLEGAL_MEM
        else
          do _ <- store_mem ptr chunk (sint32_to_vint i); returnM tt
    end.

Definition decodeM (i: int64) : M instruction := fun st =>
  match (decode_ind i) with
  | Some ins => Some (ins, st)
  | None => None
  end.

Definition get_immediate (ins:int64): M int := returnM (get_immediate ins).


Definition step : M unit :=
  do ins64<- eval_ins;
  do ins  <- decodeM ins64;
    match ins with
    | Pload chunk d s ofs =>
      do _ <- step_load_x_operation (sizeOp2chunk chunk) d s ofs;
        upd_pc_incr

    | Pstore chunk d s ofs =>
      do _ <- step_store_operation (sizeOp2chunk chunk) d s ofs;
        upd_pc_incr

    | Palu32 bop d s => jit_call_simplb

    | Pjmp ofs => do _ <- upd_pc (Vint ofs); upd_pc_incr

    | Pjmpcmp op d s ofs =>
      do b <- eval_cmp op d s;
        if b then
          do _ <- upd_pc (Vint ofs); upd_pc_incr
        else
          upd_pc_incr
    | Pcall id sg =>
      do v <- _bpf_get_call id sg;
      do _ <- upd_reg R0 v;
        upd_pc_incr

    | Pret => upd_flag BPF_SUCC_RETURN
    end.

Fixpoint bpf_interpreter_aux (fuel: nat) {struct fuel}: M unit :=
  match fuel with
  | O => upd_flag BPF_ILLEGAL_LEN
  | S fuel0 =>
    do _    <- step;
    do f    <- eval_flag;
      if flag_eq f BPF_OK then
        bpf_interpreter_aux fuel0
      else
        returnM tt
  end.

Definition bpf_interpreter (fuel: nat) (ctx_ptr: val): M val :=
  do _        <- upd_reg R1 ctx_ptr;
  do _        <- bpf_interpreter_aux fuel;
  do f        <- eval_flag;
    if flag_eq f BPF_SUCC_RETURN then
      do res  <- eval_reg R0;
        returnM res
    else
      returnM Vzero.

Close Scope monad_scope.