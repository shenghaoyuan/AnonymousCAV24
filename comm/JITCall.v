From compcert Require Import Memory Memtype Integers Values Ctypes AST.
From compcert.arm Require Import AsmSyntax ABinSem.
From Coq Require Import ZArith Lia List.

From bpf.comm Require Import Regs ListAsArray.

Open Scope Z_scope.
Import ListNotations.

Definition JITTED_LIST_MAX_LENGTH: nat := 4000.

(**r input: jitted_start_addr -> jit_state_start_addr -> result *)
Definition compcertbin_signature: signature :=
  {| sig_args := [AST.Tint; AST.Tint]; sig_res := AST.Tint; sig_cc := cc_default |}.



Definition state_block_size: Z := 52.
Definition stack_block_size: Z := 48.

Axiom jit_arm_start_address : val.

Definition get_result_bool (r:rettype) (v:aval): bool :=
  match v with
  | Cval v => is_definedb v && has_rettypeb v r
  | _     => false
  end.


Definition rbpf_copy_to (pc: int) (rs: regmap) (st_blk: block) (m: mem): option mem :=
  match Mem.store Mint32 m st_blk   0   (eval_regmap R0  rs) with
  | None => None
  | Some m0 =>
  match Mem.store Mint32 m0 st_blk  4   (eval_regmap R1  rs) with
  | None => None
  | Some m1 =>
  match Mem.store Mint32 m1 st_blk  8   (eval_regmap R2  rs) with
  | None => None
  | Some m2 =>
  match Mem.store Mint32 m2 st_blk  12  (eval_regmap R3  rs) with
  | None => None
  | Some m3 =>
  match Mem.store Mint32 m3 st_blk  16  (eval_regmap R4  rs) with
  | None => None
  | Some m4 =>
  match Mem.store Mint32 m4 st_blk  20  (eval_regmap R5  rs) with
  | None => None
  | Some m5 =>
  match Mem.store Mint32 m5 st_blk  24  (eval_regmap R6  rs) with
  | None => None
  | Some m6 =>
  match Mem.store Mint32 m6 st_blk  28  (eval_regmap R7  rs) with
  | None => None
  | Some m7 =>
  match Mem.store Mint32 m7 st_blk  32  (eval_regmap R8  rs) with
  | None => None
  | Some m8 =>
  match Mem.store Mint32 m8 st_blk  36  (eval_regmap R9  rs) with
  | None => None
  | Some m9 =>
  match Mem.store Mint32 m9 st_blk  40  (eval_regmap R10  rs) with
  | None => None
  | Some m10 => Mem.store Mint32 m10 st_blk 44 (Vint pc)
  end
  end
  end
  end
  end
  end
  end
  end
  end
  end
  end.

Definition rbpf_copy_from (rs: regmap) (st_blk: block) (m: mem): option (val * regmap) :=
  match Mem.load Mint32 m st_blk 0 with
  | None => None
  | Some v0 =>
  match Mem.load Mint32 m st_blk 4 with
  | None => None
  | Some v1 =>
  match Mem.load Mint32 m st_blk 8  with
  | None => None
  | Some v2 =>
  match Mem.load Mint32 m st_blk 12 with
  | None => None
  | Some v3 =>
  match Mem.load Mint32 m st_blk 16 with
  | None => None
  | Some v4 =>
  match Mem.load Mint32 m st_blk 20 with
  | None => None
  | Some v5 =>
  match Mem.load Mint32 m st_blk 24 with
  | None => None
  | Some v6 =>
  match Mem.load Mint32 m st_blk 28 with
  | None => None
  | Some v7 =>
  match Mem.load Mint32 m st_blk 32 with
  | None => None
  | Some v8 =>
  match Mem.load Mint32 m st_blk 36 with
  | None => None
  | Some v9 =>
  match Mem.load Mint32 m st_blk 40 with
  | None => None
  | Some v10 =>
  match Mem.load Mint32 m st_blk 44 with
  | None => None
  | Some vpc =>
    Some (vpc,
      (upd_regmap R10 v10
      (upd_regmap R9 v9
      (upd_regmap R8 v8
      (upd_regmap R7 v7
      (upd_regmap R6 v6
      (upd_regmap R5 v5
      (upd_regmap R4 v4
      (upd_regmap R3 v3
      (upd_regmap R2 v2
      (upd_regmap R1 v1
      (upd_regmap R0 v0 rs))))))))))))
  end
  end
  end
  end
  end
  end
  end
  end
  end
  end
  end
  end.


Definition jit_call_simpl (ofs: nat) (pc: int) (rs: regmap) (m: mem): option (int * regmap * mem) :=
  let fuel  := JITTED_LIST_MAX_LENGTH in
  let sz    := (Int.repr stack_block_size) in (**r 12 * 4 *)
    let (m1, st_blk) := Mem.alloc m 0 state_block_size in
      match rbpf_copy_to pc rs st_blk m1 with
      | None => None
      | Some m2 =>
        let jitted_arm_address := Val.add jit_arm_start_address
          (Vint (Int.repr (Z.of_nat (Nat.mul 4 ofs)))) (*
          (Vint (Int.mul (Int.repr (Z.of_nat ofs)) (Int.repr 2))) *) in
        let arm_argu_list_val := [jitted_arm_address; (Vptr st_blk Ptrofs.zero)] in
          match bin_exec fuel compcertbin_signature (Int.unsigned sz)
            Ptrofs.zero arm_argu_list_val m2 with
          | None => None
          | Some (_, m3) =>
            match rbpf_copy_from rs st_blk m3 with
            | None => None
            | Some (vpc, rs') =>
              match vpc with
              | Vint pc' => Some (pc', rs', m) (*
                match Mem.free m3 st_blk 0 state_block_size with
                | None => None
                | Some m' => Some (pc', rs', m')
                end *)
              | _ => None
              end
            end
          end
      end.