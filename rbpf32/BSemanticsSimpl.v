From compcert Require Import Memory Memtype Integers Values Ctypes AST.
From compcert.arm Require Import AsmSyntax ABinSem.
From Coq Require Import ZArith Lia List.

From bpf.comm Require Import Flag rBPFValues BinrBPF MemRegion.
From bpf.comm Require Import rBPFAST rBPFMemType ListAsArray JITCall.

From bpf.rbpf32 Require Import TSSyntax TSDecode BState.

Open Scope Z_scope.
Import ListNotations.

Definition check_mem_aux2 (mr: memory_region) (perm: permission) (addr: val) (chunk: memory_chunk): val :=
  let lo_ofs := Val.sub addr (start_addr mr) in
  let hi_ofs := Val.add lo_ofs (memory_chunk_to_valu32 chunk) in
    if andb (andb
              (compu_le hi_ofs (block_size mr))
              (andb (compu_le lo_ofs (memory_chunk_to_valu32_upbound chunk))
                    (comp_eq Vzero (val32_modu lo_ofs (memory_chunk_to_valu32 chunk)))))
            (perm_ge (block_perm mr) perm) then
      Val.add (block_ptr mr) lo_ofs
    else
      Vnullptr.

(**r could be may abstract *)
Fixpoint check_mem_aux (num mrs_num: nat) (perm: permission) (chunk: memory_chunk) (addr: val) (mrs: MyMemRegionsType) (m: mem) {struct num}: option val :=
  match num with
  | O => Some Vnullptr
  | S n =>
    match get_mem_region n mrs_num mrs with
    | Some cur_mr =>
      let check_ptr  := check_mem_aux2 cur_mr perm addr chunk in
        match cmp_ptr32_null m check_ptr with
        | Some is_null =>
          if is_null then
            check_mem_aux n mrs_num perm chunk addr mrs m
          else
            Some check_ptr
        | None => None
        end
    | None => None
    end
  end.

Definition check_mem (perm: permission) (chunk: memory_chunk) (addr: val) (mrs_num: nat) (mrs: MyMemRegionsType) (m: mem): option val :=
  match check_mem_aux mrs_num mrs_num perm chunk addr mrs m with
  | Some check_ptr =>
    match cmp_ptr32_null m check_ptr with
    | Some is_null =>
      if is_null then
        Some Vnullptr
      else
        Some check_ptr
    | None => None
    end
  | None => None
  end.

Definition load_mem (chunk: memory_chunk) (ptr: val) (m: mem): option val :=
  match chunk with
  | Mint8unsigned | Mint16unsigned | Mint32 =>
    match Mem.loadv chunk m ptr with
    | Some Vundef => None
    | Some res =>
      match res with
      | Vint v => Some (Vint v)
      | _ => None
      end
    | None => None
    end
  | _ => None
  end.

Definition step_load_x_operation (chunk: memory_chunk) (d: breg) (s: breg) (ofs:off) (rs: regset) (mrs_num: nat) (mrs: MyMemRegionsType) (m: mem): option (regset * bpf_flag) :=
  let addr  := Val.add (rs#s) (sint32_to_vint ofs) in
    match check_mem Readable chunk addr mrs_num mrs m with
    | None => None
    | Some ptr =>
      match cmp_ptr32_null m ptr with
      | None => None
      | Some is_null =>
        if is_null then
          Some (rs, BPF_ILLEGAL_MEM)
        else
          match load_mem chunk ptr m with
          | None => None
          | Some v =>
              Some (rs#d <- v, BPF_OK)
          end
      end
    end.

Definition store_mem (ptr: val) (chunk: memory_chunk) (v: val) (m: mem): option mem :=
  match chunk with
  | Mint8unsigned | Mint16unsigned | Mint32 => (*
    let src := vint_to_vint chunk v in *)
      Mem.storev chunk m ptr v
  | _ => None
  end.

Definition step_store_operation (chunk: memory_chunk) (d: breg) (s: breg+imm) (ofs: off) (rs: regset) (mrs_num: nat) (mrs: MyMemRegionsType) (m: mem): option (mem * bpf_flag) :=
  let addr := Val.add (rs#d) (sint32_to_vint ofs) in
    match s with
    | inl r =>
      match check_mem Writable chunk addr mrs_num mrs m with
      | None => None
      | Some ptr =>
        match cmp_ptr32_null m ptr with
        | None => None
        | Some is_null =>
          if is_null then
            Some (m, BPF_ILLEGAL_MEM)
          else
            match store_mem ptr chunk (rs#r) m with
            | None => None
            | Some m' => Some (m', BPF_OK)
            end
        end
      end
    | inr i =>
      match check_mem Writable chunk addr mrs_num mrs m with
      | None => None
      | Some ptr =>
        match cmp_ptr32_null m ptr with
        | None => None
        | Some is_null =>
          if is_null then
            Some (m, BPF_ILLEGAL_MEM)
          else
            match store_mem ptr chunk (sint32_to_vint i) m with
            | None => None
            | Some m' => Some (m', BPF_OK)
            end
        end
      end
    end.

Definition eval_ins (rs: regset) (l: list int64) (len: nat): option int64 :=
  match rs#BPC with
  | Vint pc =>
    if (Int.cmpu Clt pc (Int.repr (Z.of_nat len))) then
      List.nth_error l (Z.to_nat (Int.unsigned pc))
    else
      None
  | _ => None
  end.

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

Definition step (l: list int64) (kv: list nat) (len: nat) (rs: regset) (mrs_num: nat) (mrs: MyMemRegionsType) (m: mem):
  option (regset * mem * bpf_flag) :=
  match eval_ins rs l len with
  | None => None
  | Some ins64 =>
    match decode_ind ins64 with
    | None => None
    | Some ins =>
      match ins with
      | Pload chunk d s ofs =>
        match step_load_x_operation (sizeOp2chunk chunk) d s ofs rs mrs_num mrs m with
        | None => None
        | Some (rs', f) => Some (nextinstr rs', m, f)
        end

      | Pstore chunk d s ofs =>
        match step_store_operation (sizeOp2chunk chunk) d s ofs rs mrs_num mrs m with
        | None => None
        | Some (m, f) => Some (nextinstr rs, m, f)
        end

      | Palu32 bop d s =>
        match jit_call_simplb kv rs m with
        | None => None
        | Some (rs', m') => Some ((*nextinstr *) rs', m', BPF_OK)
        end

      | Pjmp ofs => Some (rs#BPC <- (Val.add (Val.add rs#BPC (Vint ofs)) Vone), m, BPF_OK)

      | Pjmpcmp op d s ofs =>
        match TSSyntax.eval_cmp op rs m d s with
        | None => None
        | Some b =>
          if b then
            Some (rs#BPC <- (Val.add (Val.add rs#BPC (Vint ofs)) Vone), m, BPF_OK)
          else
            Some (nextinstr rs, m, BPF_OK)
        end
      | Pcall id sg =>
        match _bpf_get_call id sg m with
        | Some (Vint v, m1) => Some (nextinstr (rs # R0 <- (Vint v)), m1, BPF_OK)
        | _ => None
        end

      | Pret => Some (rs, m, BPF_SUCC_RETURN)
      end
    end
  end.

Fixpoint bpf_interpreter_aux (fuel: nat) (l: list int64) (len: nat) (kv: list nat) (jit_ins: list int)
  (rs: regset) (mrs_num: nat) (mrs: MyMemRegionsType) (m: mem) {struct fuel}: option (regset * mem * bpf_flag) :=
  match fuel with
  | O => Some (rs, m, BPF_ILLEGAL_LEN)
  | S fuel0 =>
      match step l kv len rs mrs_num mrs m with
      | None => None
      | Some (rs', m' ,f') =>
        if flag_eq f' BPF_OK then
          bpf_interpreter_aux fuel0 l len kv jit_ins rs' mrs_num mrs m'
        else
          Some (rs', m', f')
      end
  end.

Definition bpf_interpreter (fuel: nat) (ctx_ptr: val) (l: list int64) (len: nat)
   (tp_kv: list nat) (tp_bin: list int) (rs: regset) (mrs_num: nat)
  (mrs: MyMemRegionsType) (m: mem): option (val * regset * mem * bpf_flag) :=
  let rs1 := rs#R1 <- ctx_ptr in
    match bpf_interpreter_aux fuel l len tp_kv tp_bin rs1 mrs_num mrs m with
    | None => None
    | Some (rs', m' ,f') =>
      if flag_eq f' BPF_SUCC_RETURN then
        Some (rs'#R0, rs', m', f')
      else
        Some (Vzero, rs', m', f')
    end.