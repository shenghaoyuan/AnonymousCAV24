From compcert Require Import Integers.
From compcert.arm Require Import AsmSyntax BinSyntax BinDecode.

From bpf.comm Require Import Flag BinrBPF ListAsArray Regs.
From bpf.rbpf32 Require Import TSSyntax TSDecode JITConfig.
From bpf.jit Require Import Arm32Reg ThumbInsOp ListSetRefinement ThumbJIT ThumbJIT1.

From Coq Require Import List ZArith Arith String.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope asm.

Definition tp_bin_add := List32.assign'.

Definition jit_alu32_pre2 (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code) :=
  let ins_rdn := encode_arm32 (Int.repr 4) MOV_R_OP 0 3 in
  let ins_rm  := encode_arm32 Int.one  ins_rdn 3 4 in
  let ins     := encode_arm32 Int.one ins_rm 7 1 in
  let ins32   := encode_arm32 ins NOP_OP 16 16 in
  let str   := jit_alu32_thumb_mem_template_jit STR_I_OP (Int.repr 11) (int_of_ireg SP) (Int.repr 44) in
    match tp_bin_add tp_bin tp_len ins32 with
    | None => None
    | Some tp_bin1 =>
      match tp_bin_add tp_bin1 (S tp_len) str with
      | None => None
      | Some tp2 => Some (Nat.add tp_len 2, tp2)
      end
    end.

Definition jit_call_save_add2 (r: breg) (ls: listset_regmap)
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code) :=
  if eval_listset_regmap r ls then
    Some (tp_len, tp_bin)
  else
    let ldr_ins := jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg r) (int_of_ireg IR12)
                  (Int.mul (int_of_breg r) (Int.repr 4)) in
      if (Int.ltu (Int.repr 3) (int_of_breg r)) && (Int.ltu (int_of_breg r) (int_of_ireg IR12)) then
        let str_ins := jit_alu32_thumb_mem_template_jit STR_I_OP (int_of_breg r) (int_of_ireg SP)
                      (Int.mul (int_of_breg r) (Int.repr 4)) in
          match tp_bin_add tp_bin tp_len str_ins with
          | None => None
          | Some tp_bin1 =>
            match tp_bin_add tp_bin1 (S tp_len) ldr_ins with
            | None => None
            | Some tp2 => Some (Nat.add tp_len 2, tp2)
            end
          end
        else
          match tp_bin_add tp_bin tp_len ldr_ins with
          | None => None
          | Some tp_bin1 => Some (Nat.add tp_len 1, tp_bin1)
          end.

Definition jit_call_save_reg2 (dst src: breg) (ld_set st_set: listset_regmap)
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code * listset_regmap * listset_regmap):=
  match jit_call_save_add2 dst ld_set tp_len tp_bin with
  | None => None
  | Some (tp_len1, tp_bin1) =>
    let ld_set1 := listset_add_regmap dst ld_set in
    let st_set1 := listset_add_regmap dst st_set in
      match jit_call_save_add2 src ld_set1 tp_len1 tp_bin1 with
      | None => None
      | Some (tp_len2, tp_bin2) =>
        let ld_set2 := listset_add_regmap src ld_set1 in
          Some (tp_len2, tp_bin2, ld_set2, st_set1)
      end
  end.

Definition jit_call_save_imm2 (dst: breg) (ld_set st_set: listset_regmap)
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code * listset_regmap * listset_regmap):=
  match jit_call_save_add2 dst ld_set tp_len tp_bin with
  | None => None
  | Some (tp_len1, tp_bin1) =>
    Some (tp_len1, tp_bin1, listset_add_regmap dst ld_set, listset_add_regmap dst st_set)
  end.


Definition bpf_alu32_to_thumb_reg2 (op: aluOp) (dst: breg) (src: ireg)
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code) :=
  match op with
  | ADD   =>
    let d       := if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one in
    let rdn     := if Int.lt (int_of_breg dst) (Int.repr 8) then
                      (int_of_breg dst)
                    else
                      Int.sub (int_of_breg dst) (Int.repr 8) in
    let ins_rdn := encode_arm32 rdn ADD_R_OP 0 3 in
    let ins_rm  := encode_arm32 (int_of_ireg src) ins_rdn 3 4 in
    let ins     := encode_arm32 d ins_rm 7 1 in
    let ins32   := encode_arm32 ins NOP_OP 16 16 in
      match tp_bin_add tp_bin tp_len ins32 with
      | None => None
      | Some tp_bin1 => Some (Nat.add tp_len 1, tp_bin1)
      end
  | SUB   =>
    match tp_bin_add tp_bin tp_len (bpf_alu32_to_thumb_reg_comm SUB_R_OP dst src) with
    | None => None
    | Some tp_bin1 => Some (Nat.add tp_len 1, tp_bin1)
    end
  | MUL   =>
    let ins_lo  := encode_arm32 (int_of_breg dst) MUL_OP 0 4 in
    let ins_hi0 := encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4 in
    let ins_hi  := encode_arm32 (Int.repr 0xf) ins_hi0 12 4 in
    let ins32   := encode_arm32 ins_hi ins_lo 16 16 in
      match tp_bin_add tp_bin tp_len ins32 with
      | None => None
      | Some tp_bin1 => Some (Nat.add tp_len 1, tp_bin1)
      end
  | DIV   => None

  | OR    =>
    match tp_bin_add tp_bin tp_len (bpf_alu32_to_thumb_reg_comm ORR_R_OP dst src) with
    | None => None
    | Some tp_bin1 => Some (Nat.add tp_len 1, tp_bin1)
    end
  | AND   =>
    match tp_bin_add tp_bin tp_len (bpf_alu32_to_thumb_reg_comm AND_R_OP dst src) with
    | None => None
    | Some tp_bin1 => Some (Nat.add tp_len 1, tp_bin1)
    end
  | LSH   => None
  | RSH   => None
  | NEG   => None
  | MOD   => None
  | XOR   =>
    match tp_bin_add tp_bin tp_len (bpf_alu32_to_thumb_reg_comm EOR_R_OP dst src) with
    | None => None
    | Some tp_bin1 => Some (Nat.add tp_len 1, tp_bin1)
    end
  | MOV   =>
    (**r optimization: for `mov ri ri`, we generate nothing *)
    if reg_ireg_eqb dst src then
      Some (tp_len, tp_bin)
    else
      let d       := if Int.lt (int_of_breg dst) (Int.repr 8) then Int.zero else Int.one in
      let rdn     := if Int.lt (int_of_breg dst) (Int.repr 8) then
                        (int_of_breg dst)
                      else
                        Int.sub (int_of_breg dst) (Int.repr 8) in
      let ins_rdn := encode_arm32 rdn MOV_R_OP 0 3 in
      let ins_rm  := encode_arm32 (int_of_ireg src)  ins_rdn 3 4 in
      let ins     := encode_arm32 d ins_rm 7 1 in
      let ins32   := encode_arm32 ins NOP_OP 16 16 in
        match tp_bin_add tp_bin tp_len ins32 with
        | None => None
        | Some tp_bin1 => Some (Nat.add tp_len 1, tp_bin1)
        end
  | ARSH  => None
  end.

Definition bpf_alu32_to_thumb_imm_comm2 (op: int) (alu_op: aluOp) (dst: breg) (imm32: int)
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code) :=
  if (Int.cmpu Cle Int.zero imm32) && (Int.cmpu Cle imm32 (Int.repr 255)) then (**r 0 <= imm32 <= 255 *)
    let ins_lo    := encode_arm32 (int_of_breg dst) op 0 4 in
    let ins_hi    := encode_arm32 (int_of_breg dst) imm32 8 4 in
    let ins32     := encode_arm32 ins_hi ins_lo 16 16 in
      match tp_bin_add tp_bin tp_len ins32 with
      | None => None
      | Some tp_bin1 => Some (Nat.add tp_len 1, tp_bin1)
      end
  else
    let lo_32 := decode_arm32 imm32 0 16 in
    let hi_32 := decode_arm32 imm32 16 16 in
      if Int.eq lo_32 imm32 then (**r optimization: if high_16 = 0 then only add `movw` *)
        match tp_bin_add tp_bin tp_len (mov_int_to_movwt lo_32 IR11 MOVW_OP) with
        | None => None
        | Some tp_bin1 =>
          bpf_alu32_to_thumb_reg2 alu_op dst IR11 (Nat.add tp_len 1) tp_bin1
        end
      else (**r optimization: if high_16 <> 0 then add`movt + movw` *)
        match tp_bin_add tp_bin tp_len (mov_int_to_movwt lo_32 IR11 MOVW_OP) with
        | None => None
        | Some tp_bin1 =>
          match tp_bin_add tp_bin (Nat.add tp_len 1) (mov_int_to_movwt hi_32 IR11 MOVT_OP) with
          | None => None
          | Some tp_bin2 =>
            bpf_alu32_to_thumb_reg2 alu_op dst IR11 (Nat.add tp_len 2) tp_bin2
          end
        end.

Definition bpf_alu32_to_thumb_imm_shift_comm2 (op: int) (dst: breg) (imm32: int)
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code) :=
  if (Int.cmpu Cle Int.zero imm32) && (Int.cmpu Clt imm32 (Int.repr 32)) then
    let ins_lo  := encode_arm32 (int_of_breg dst) op 0 4 in
    let ins_hi0 := encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4 in
    let ins_hi  := encode_arm32 (Int.repr 0xf) ins_hi0 12 4 in
    let ins32   := encode_arm32 ins_hi ins_lo 16 16 in
      match tp_bin_add tp_bin tp_len (mov_int_to_movwt imm32 IR11 MOVW_OP) with
      | None => None
      | Some tp_bin1 =>
        match tp_bin_add tp_bin (Nat.add tp_len 1) ins32 with
        | None => None
        | Some tp_bin2 => Some ((Nat.add tp_len 2), tp_bin2)
        end
      end
  else
    None.

Definition bpf_alu32_to_thumb_imm2 (op: aluOp) (dst: breg) (imm32: int)
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code) :=
  match op with
  | ADD   => bpf_alu32_to_thumb_imm_comm2 ADD_I_OP ADD dst imm32 tp_len tp_bin
  | SUB   => bpf_alu32_to_thumb_imm_comm2 SUB_I_OP SUB dst imm32 tp_len tp_bin
  | MUL   => (**r CompCert doesn't have mul_imm, so we do `mov + mul_reg` *)
    let lo_32 := decode_arm32 imm32 0 16 in
    let hi_32 := decode_arm32 imm32 16 16 in
      if Int.eq lo_32 imm32 then (**r optimization: if high_16 = 0 then only add `movw` *)
        match tp_bin_add tp_bin tp_len (mov_int_to_movwt lo_32 IR11 MOVW_OP) with
        | None => None
        | Some tp_bin1 =>
          bpf_alu32_to_thumb_reg2 MUL dst IR11 (Nat.add tp_len 1) tp_bin1
        end
      else
        match tp_bin_add tp_bin tp_len (mov_int_to_movwt lo_32 IR11 MOVW_OP) with
        | None => None
        | Some tp_bin1 =>
          match tp_bin_add tp_bin (Nat.add tp_len 1) (mov_int_to_movwt hi_32 IR11 MOVT_OP) with
          | None => None
          | Some tp_bin2 =>
            bpf_alu32_to_thumb_reg2 MUL dst IR11 (Nat.add tp_len 2) tp_bin2
          end
        end

  | DIV   => (**r CompCert doesn't have div_imm, so we do `mov + div_reg` *)
    if Int.eq imm32 Int.zero then
      None
    else 
      (**r construct: udiv Rd Rn Rm *)
      let ins_lo  := encode_arm32 (int_of_breg dst) UDIV_LO_OP 0 4 in
      let ins_hi0 := encode_arm32 (int_of_breg dst) UDIV_HI_OP 8 4 in
      let ins_hi  := encode_arm32 (int_of_ireg IR11) ins_hi0 0 4 in
      let ins32   := encode_arm32 ins_hi ins_lo 16 16 in

      let lo_32 := decode_arm32 imm32 0 16 in
      let hi_32 := decode_arm32 imm32 16 16 in
        if Int.eq lo_32 imm32 then (**r optimization: if high_16 = 0 then only add `movw` *)
          match tp_bin_add tp_bin tp_len (mov_int_to_movwt lo_32 IR11 MOVW_OP) with
          | None => None
          | Some tp_bin1 =>
            match tp_bin_add tp_bin (Nat.add tp_len 1) ins32 with
            | None => None
            | Some tp_bin2 => Some ((Nat.add tp_len 2), tp_bin2)
            end
          end
        else
          match tp_bin_add tp_bin tp_len (mov_int_to_movwt lo_32 IR11 MOVW_OP) with
          | None => None
          | Some tp_bin1 =>
            match tp_bin_add tp_bin (Nat.add tp_len 1) (mov_int_to_movwt hi_32 IR11 MOVT_OP) with
            | None => None
            | Some tp_bin2 =>
              match tp_bin_add tp_bin (Nat.add tp_len 2) ins32 with
              | None => None
              | Some tp_bin3 => Some ((Nat.add tp_len 3), tp_bin3)
              end
            end
          end

  | OR    => bpf_alu32_to_thumb_imm_comm2 ORR_I_OP OR  dst imm32 tp_len tp_bin
  | AND   => bpf_alu32_to_thumb_imm_comm2 AND_I_OP AND dst imm32 tp_len tp_bin
  | LSH   => bpf_alu32_to_thumb_imm_shift_comm2 LSL_R_OP dst imm32 tp_len tp_bin
  | RSH   => bpf_alu32_to_thumb_imm_shift_comm2 LSR_R_OP dst imm32 tp_len tp_bin
  | NEG   =>
    let ins_lo    := encode_arm32 (int_of_ireg IR11) RSB_I_OP 0 4 in (**r dst = 0 - IR11 *)
    let ins_hi    := encode_arm32 (int_of_breg dst) Int.zero 8 4 in
    let ins32     := encode_arm32 ins_hi ins_lo 16 16 in
    let lo_32 := decode_arm32 imm32 0 16 in
    let hi_32 := decode_arm32 imm32 16 16 in
      if Int.eq lo_32 imm32 then (**r optimization: if high_16 = 0 then only add `movw` *)
        match tp_bin_add tp_bin tp_len (mov_int_to_movwt lo_32 IR11 MOVW_OP) with
        | None => None
        | Some tp_bin1 =>
          match tp_bin_add tp_bin (Nat.add tp_len 1) ins32 with
          | None => None
          | Some tp_bin2 => Some ((Nat.add tp_len 2), tp_bin2)
          end
        end
      else
        match tp_bin_add tp_bin tp_len (mov_int_to_movwt lo_32 IR11 MOVW_OP) with
        | None => None
        | Some tp_bin1 =>
          match tp_bin_add tp_bin (Nat.add tp_len 1) (mov_int_to_movwt hi_32 IR11 MOVT_OP) with
          | None => None
          | Some tp_bin2 => 
            match tp_bin_add tp_bin (Nat.add tp_len 2) ins32 with
            | None => None
            | Some tp_bin3 => Some ((Nat.add tp_len 3), tp_bin3)
            end
          end
        end
  | MOD   => None
  | XOR   => bpf_alu32_to_thumb_imm_comm2 EOR_I_OP XOR dst imm32 tp_len tp_bin
  | MOV   =>
    let lo_32 := decode_arm32 imm32 0 16 in
    let hi_32 := decode_arm32 imm32 16 16 in
      if Int.eq lo_32 imm32 then (**r optimization: if high_16 = 0 then only add `movw` *)
        match tp_bin_add tp_bin tp_len (mov_int_to_movwt lo_32 (ireg_of_breg dst) MOVW_OP) with
        | None => None
        | Some tp_bin1 => Some ((Nat.add tp_len 1), tp_bin1)
        end
      else
        match tp_bin_add tp_bin tp_len (mov_int_to_movwt lo_32 (ireg_of_breg dst) MOVW_OP) with
        | None => None
        | Some tp_bin1 =>
          match tp_bin_add tp_bin (Nat.add tp_len 1) (mov_int_to_movwt hi_32 (ireg_of_breg dst) MOVT_OP) with
          | None => None
          | Some tp_bin2 => Some ((Nat.add tp_len 2), tp_bin2)
          end
        end
  | ARSH  => bpf_alu32_to_thumb_imm_shift_comm2 ASR_R_OP dst imm32 tp_len tp_bin
  end.


Definition jit_one2 (op:aluOp) (dst: breg) (src: breg+imm) (ld_set st_set: listset_regmap)
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code * listset_regmap * listset_regmap):=
  match src with
  | inl r =>
    match jit_call_save_reg2 dst r ld_set st_set tp_len tp_bin with
    | None => None
    | Some (tp_len1, tp_bin1, ld_set1, st_set1) =>
      match bpf_alu32_to_thumb_reg2 op dst (ireg_of_breg r) tp_len1 tp_bin1 with
      | None => None
      | Some (tp_len2, tp_bin2) => Some (tp_len2, tp_bin2, ld_set1, st_set1)
      end
    end
  | inr i =>
    match jit_call_save_imm2 dst ld_set st_set tp_len tp_bin with
    | None => None
    | Some (tp_len1, tp_bin1, ld_set1, st_set1) =>
      match bpf_alu32_to_thumb_imm2 op dst i tp_len1 tp_bin1 with
      | None => None
      | Some (tp_len2, tp_bin2) => Some (tp_len2, tp_bin2, ld_set1, st_set1)
      end
    end
  end.


Definition jit_alu32_thumb_pc_add2 (imm32: int)
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code) :=
  if (Int.cmpu Cle Int.zero imm32) && (Int.cmpu Cle imm32 (Int.repr 255)) then (**r 0 <= imm32 <= 255 *)
    let ins_lo    := encode_arm32 (Int.repr 11) ADD_I_OP 0 4 in
    let ins_hi    := encode_arm32 (Int.repr 11) imm32 8 4 in
    let ins32     := encode_arm32 ins_hi ins_lo 16 16 in
      match tp_bin_add tp_bin tp_len ins32 with
      | None => None
      | Some tp_bin1 => Some ((Nat.add tp_len 1), tp_bin1)
      end
  else
    None.

Definition jit_alu32_thumb_pc2 (num: nat)
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code) :=
  let l_ldr := jit_alu32_thumb_mem_template_jit LDR_I_OP
    (Int.repr 11) (int_of_ireg IR12) (Int.repr 44) in
      match tp_bin_add tp_bin tp_len l_ldr with
      | None => None
      | Some tp_bin1 =>
        match jit_alu32_thumb_pc_add2 (Int.repr (Z.of_nat num)) (Nat.add tp_len 1) tp_bin1 with
        | None => None
        | Some (tp_len2, tp_bin2) =>
          let l_str := jit_alu32_thumb_mem_template_jit STR_I_OP
            (Int.repr 11) (int_of_ireg IR12) (Int.repr 44) in
            match tp_bin_add tp_bin2 tp_len2 l_str with
            | None => None
            | Some tp_bin3 => Some ((Nat.add tp_len2 1), tp_bin3)
            end
        end
      end.

Definition jit_alu32_thumb_upd_store (r: breg) (st_set: listset_regmap)
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code) :=
  if eval_listset_regmap r st_set then
    match tp_bin_add tp_bin tp_len (jit_alu32_thumb_mem_template_jit STR_I_OP (int_of_breg r) (int_of_ireg IR12)
                    (Int.mul (int_of_breg r) (Int.repr 4))) with
    | None => None
    | Some tp_bin1 => Some ((Nat.add tp_len 1), tp_bin1)
    end
  else
    Some (tp_len, tp_bin).

Definition jit_alu32_thumb_store2 (st_set: listset_regmap)
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code) :=
  match jit_alu32_thumb_upd_store R0 st_set tp_len tp_bin with
  | None => None
  | Some (tp_len1, tp_bin1) =>
    match jit_alu32_thumb_upd_store R1 st_set tp_len1 tp_bin1 with
    | None => None
    | Some (tp_len2, tp_bin2) =>
    match jit_alu32_thumb_upd_store R2 st_set tp_len2 tp_bin2 with
    | None => None
    | Some (tp_len3, tp_bin3) =>
    match jit_alu32_thumb_upd_store R3 st_set tp_len3 tp_bin3 with
    | None => None
    | Some (tp_len4, tp_bin4) =>
    match jit_alu32_thumb_upd_store R4 st_set tp_len4 tp_bin4 with
    | None => None
    | Some (tp_len5, tp_bin5) =>
    match jit_alu32_thumb_upd_store R5 st_set tp_len5 tp_bin5 with
    | None => None
    | Some (tp_len6, tp_bin6) =>
    match jit_alu32_thumb_upd_store R6 st_set tp_len6 tp_bin6 with
    | None => None
    | Some (tp_len7, tp_bin7) =>
    match jit_alu32_thumb_upd_store R7 st_set tp_len7 tp_bin7 with
    | None => None
    | Some (tp_len8, tp_bin8) =>
    match jit_alu32_thumb_upd_store R8 st_set tp_len8 tp_bin8 with
    | None => None
    | Some (tp_len9, tp_bin9) =>
    match jit_alu32_thumb_upd_store R9 st_set tp_len9 tp_bin9 with
    | None => None
    | Some (tp_len10, tp_bin10) =>
      jit_alu32_thumb_upd_store R10 st_set tp_len10 tp_bin10
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

(** * Reset Stage: recover the initial value of selected arm32 registers *)

Definition jit_alu32_thumb_upd_reset (r: breg) (ld_set: listset_regmap)
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code) :=
  if eval_listset_regmap r ld_set then
    match tp_bin_add tp_bin tp_len (jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg r) (int_of_ireg IR13)
                      (Int.mul (int_of_breg r) (Int.repr 4))) with
    | None => None
    | Some tp_bin1 => Some ((Nat.add tp_len 1), tp_bin1)
    end
  else
    Some (tp_len, tp_bin).

Definition jit_alu32_thumb_reset12 (ld_set: listset_regmap)
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code) :=
  match jit_alu32_thumb_upd_reset R4 ld_set tp_len tp_bin with
  | None => None
  | Some (tp_len5, tp_bin5) =>
    match jit_alu32_thumb_upd_reset R5 ld_set tp_len5 tp_bin5 with
    | None => None
    | Some (tp_len6, tp_bin6) =>
    match jit_alu32_thumb_upd_reset R6 ld_set tp_len6 tp_bin6 with
    | None => None
    | Some (tp_len7, tp_bin7) =>
    match jit_alu32_thumb_upd_reset R7 ld_set tp_len7 tp_bin7 with
    | None => None
    | Some (tp_len8, tp_bin8) =>
    match jit_alu32_thumb_upd_reset R8 ld_set tp_len8 tp_bin8 with
    | None => None
    | Some (tp_len9, tp_bin9) =>
    match jit_alu32_thumb_upd_reset R9 ld_set tp_len9 tp_bin9 with
    | None => None
    | Some (tp_len10, tp_bin10) =>
      jit_alu32_thumb_upd_reset R10 ld_set tp_len10 tp_bin10
    end
    end
    end
    end
    end
    end.

Definition jit_alu32_thumb_reset2 (ld_set: listset_regmap)
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code) :=
  let l_ldr := jit_alu32_thumb_mem_template_jit LDR_I_OP (Int.repr 11) (int_of_ireg IR13) (Int.repr 44) in
    match tp_bin_add tp_bin tp_len l_ldr with
    | None => None
    | Some tp_bin1 => jit_alu32_thumb_reset12 ld_set (Nat.add tp_len 1) tp_bin1
    end.

Definition jit_alu32_post2
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code) :=
  let l_ldr := jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_ireg SP) (int_of_ireg SP) Int.zero in
  let ins_rm   := encode_arm32 (int_of_ireg RA) BX_OP 3 4 in
  let ins32    := encode_arm32 ins_rm NOP_OP 16 16 in
    match tp_bin_add tp_bin tp_len l_ldr with
    | None => None
    | Some tp_bin1 =>
      match tp_bin_add tp_bin1 (Nat.add tp_len 1) ins32 with
      | None => None
      | Some tp_bin2 => Some (Nat.add tp_len 2, tp_bin2)
      end
    end.

Close Scope asm.
Close Scope bool_scope.
Close Scope Z_scope.