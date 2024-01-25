From compcert Require Import Memory Memtype Integers Values Ctypes AST.
From compcert.arm Require Import AsmSyntax ABinSem.
From Coq Require Import ZArith Lia List.

From bpf.comm Require Import Regs ListAsArray rBPFMemType.

Open Scope Z_scope.
Import ListNotations.

Definition JITTED_LIST_MAX_LENGTH: nat := 4000.

(**r input: jitted_start_addr -> jit_state_start_addr -> result *)
Definition compcertbin_signature: signature :=
  {| sig_args := [AST.Tint; AST.Tint]; sig_res := AST.Tint; sig_cc :=
    {| AST.cc_vararg := Some 1%Z; AST.cc_unproto := false; AST.cc_structret := false |} |}.



Definition state_block_size: Z := 52.
Definition stack_block_size: Z := 48.

Axiom jit_arm_block : block.
Axiom jit_state_block : block.

Definition get_result_bool (r:rettype) (v:aval): bool :=
  match v with
  | Cval v => is_definedb v && has_rettypeb v r
  | _     => false
  end.

Definition store_vint (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val): option mem :=
  match v with
  | Vint vi => Mem.store chunk m b ofs v
  | _ => None
  end.

Definition rbpf_copy_to (pc: int) (rs: regmap) (st_blk: block) (m: mem): option mem :=
  match store_vint Mint32 m st_blk   0   (eval_regmap R0  rs) with
  | None => None
  | Some m0 =>
  match store_vint Mint32 m0 st_blk  4   (eval_regmap R1  rs) with
  | None => None
  | Some m1 =>
  match store_vint Mint32 m1 st_blk  8   (eval_regmap R2  rs) with
  | None => None
  | Some m2 =>
  match store_vint Mint32 m2 st_blk  12  (eval_regmap R3  rs) with
  | None => None
  | Some m3 =>
  match store_vint Mint32 m3 st_blk  16  (eval_regmap R4  rs) with
  | None => None
  | Some m4 =>
  match store_vint Mint32 m4 st_blk  20  (eval_regmap R5  rs) with
  | None => None
  | Some m5 =>
  match store_vint Mint32 m5 st_blk  24  (eval_regmap R6  rs) with
  | None => None
  | Some m6 =>
  match store_vint Mint32 m6 st_blk  28  (eval_regmap R7  rs) with
  | None => None
  | Some m7 =>
  match store_vint Mint32 m7 st_blk  32  (eval_regmap R8  rs) with
  | None => None
  | Some m8 =>
  match store_vint Mint32 m8 st_blk  36  (eval_regmap R9  rs) with
  | None => None
  | Some m9 =>
  match store_vint Mint32 m9 st_blk  40  (eval_regmap R10  rs) with
  | None => None
  | Some m10 => store_vint Mint32 m10 st_blk 44 (Vint pc)
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

Definition load_vint (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z): option val :=
  match Mem.load chunk m b ofs with
  | Some (Vint vi) => Some (Vint vi)
  | _ => None
  end.

Definition rbpf_copy_from (rs: regmap) (st_blk: block) (m: mem): option (val * regmap) :=
  match load_vint Mint32 m st_blk 0 with
  | None => None
  | Some v0 =>
  match load_vint Mint32 m st_blk 4 with
  | None => None
  | Some v1 =>
  match load_vint Mint32 m st_blk 8  with
  | None => None
  | Some v2 =>
  match load_vint Mint32 m st_blk 12 with
  | None => None
  | Some v3 =>
  match load_vint Mint32 m st_blk 16 with
  | None => None
  | Some v4 =>
  match load_vint Mint32 m st_blk 20 with
  | None => None
  | Some v5 =>
  match load_vint Mint32 m st_blk 24 with
  | None => None
  | Some v6 =>
  match load_vint Mint32 m st_blk 28 with
  | None => None
  | Some v7 =>
  match load_vint Mint32 m st_blk 32 with
  | None => None
  | Some v8 =>
  match load_vint Mint32 m st_blk 36 with
  | None => None
  | Some v9 =>
  match load_vint Mint32 m st_blk 40 with
  | None => None
  | Some v10 =>
  match load_vint Mint32 m st_blk 44 with
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
    match rbpf_copy_to pc rs jit_state_block m with
    | None => None
    | Some m2 =>
      let arm_argu_list_val :=
        [ (Vptr jit_arm_block (Ptrofs.mul (Ptrofs.repr 4)
            (Ptrofs.of_intu (Int.repr (Z.of_nat ofs)))));
          (Vptr jit_state_block Ptrofs.zero)] in
        match bin_exec fuel compcertbin_signature (Int.unsigned sz)
          Ptrofs.zero arm_argu_list_val m2 with
        | None => None
        | Some (_, m3) =>
          match rbpf_copy_from rs jit_state_block m3 with
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

Lemma store_vint_unchanged_on:
  forall chunk m1 st_blk ofs v m2 m (P: block -> Z -> Prop)
    (Hstore : store_vint chunk m1 st_blk ofs v = Some m2)
    (Hblk_neq: forall ofs, ~P st_blk ofs)
    (munchange : Mem.unchanged_on P m1 m),
      Mem.unchanged_on P m2 m.
Proof.
  unfold store_vint.
  intros.
  destruct v; inversion Hstore.
  clear H0.
  eapply store_unchanged_on_4; eauto.
Qed.

Lemma rbpf_copy_to_unchanged_on:
  forall pc rs st_blk m1 m2 m (P: block -> Z -> Prop)
    (Hcopy_to : rbpf_copy_to pc rs st_blk m1 = Some m2)
    (Hblk_neq: forall ofs, ~P st_blk ofs)
    (munchange : Mem.unchanged_on P m1 m),
      Mem.unchanged_on P m2 m.
Proof.
  unfold rbpf_copy_to.
  intros.
  repeat (destruct store_vint eqn: Hn_eq; [
    eapply store_vint_unchanged_on in Hn_eq; eauto;
    clear munchange; rename Hn_eq into munchange |
    inversion Hcopy_to ]).
  inversion Hcopy_to.
  subst m2; auto.
Qed.