From compcert Require Import Integers.
From compcert.arm Require Import AsmSyntax BinSyntax BinDecode.

From bpf.comm Require Import Flag BinrBPF ListAsArray Regs.
From bpf.rbpf32 Require Import TSSyntax TSDecode JITConfig.
From bpf.jit Require Import Arm32Reg ThumbInsOp.

From Coq Require Import List ZArith Arith String FSetList.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope asm.

Definition list_bin_insert := List32.assign'.

Definition jit_alu32_thumb_mem_template_jit (op rt rn imm12: int): int :=
  let str_low   := encode_arm32 rn op 0 4 in
  let str_high  := encode_arm32 rt imm12 12 4 in
    encode_arm32 str_high str_low 16 16.

(** * Pre Stage: mov *)

Definition jit_alu32_pre (b_pc: nat) (bl: bin_code): option (nat * bin_code) :=
  (* the allocation will do `STR IR12 [SP, #+0]` *)
  (**r MOV IR12 R1 *) (**r 12 = 0b 1100 *)
  let ins_rdn := encode_arm32 (Int.repr 4) MOV_R_OP 0 3 in
  let ins_rm  := encode_arm32 Int.one  ins_rdn 3 4 in
  let ins     := encode_arm32 Int.one ins_rm 7 1 in
  let ins32   := encode_arm32 ins NOP_OP 16 16 in

  (**r STR IR11 [SP, #44] *)
  let str   := jit_alu32_thumb_mem_template_jit STR_I_OP (Int.repr 11) (int_of_ireg SP) (Int.repr 44) in
    match list_bin_insert bl b_pc ins32 with
    | None => None
    | Some bl1 =>
      match list_bin_insert bl (S b_pc) str with
      | None => None
      | Some bl2 => Some (S (S b_pc), bl2)
      end
    end.

(** * Jitted Code: from BPF alu32 to thumb alu *)

Definition jit_call_save_add (r: breg) (ls: listset): bin_code :=
  if set_mem breg_eq r ls then
    []
  else
    (**r determine if we should do calling_convention, depends on r [4, 11] *) (*
    if (Int.ltu (Int.repr 3) (int_of_reg r)) && (Int.ltu (int_of_reg r) (int_of_ireg IR12)) then *)
    let ldr_ins := jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg r) (int_of_ireg IR12)
                  (Int.mul (int_of_breg r) (Int.repr 4)) in
      if set_mem ireg_eq (ireg_of_breg r) arm_callee_save then
        let str_ins := jit_alu32_thumb_mem_template_jit STR_I_OP (int_of_breg r) (int_of_ireg SP)
                      (Int.mul (int_of_breg r) (Int.repr 4)) in
          [str_ins; ldr_ins]
        else
          [ldr_ins].

Definition jit_call_save_reg (dst src: breg) (ld_set st_set: listset): bin_code * listset * listset :=
  let l1 := jit_call_save_add dst ld_set in
  let ld_set1 := set_add breg_eq dst ld_set in
  let st_set1 := set_add breg_eq dst st_set in

  let l2 := jit_call_save_add src ld_set1 in
  let ld_set2 := set_add breg_eq src ld_set1 in
    (l1 ++ l2, ld_set2, st_set1).

Definition jit_call_save_imm (dst: breg) (ld_set st_set: listset): bin_code * listset * listset :=
  let l1 := jit_call_save_add dst (set_union breg_eq ld_set st_set) in
    (l1, set_add breg_eq dst ld_set, set_add breg_eq dst st_set).

Definition bpf_alu32_to_thumb_reg_comm (op: int) (dst: breg) (src: ireg) : int :=
  let ins_lo  := encode_arm32 (int_of_breg dst) op 0 4 in
  let ins_hi  := encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4 in
    encode_arm32 ins_hi ins_lo 16 16.

(**r src may be IR11 because of bpf_alu32_to_thumb_imm *)
Definition bpf_alu32_to_thumb_reg (op: aluOp) (dst: breg) (src: ireg): option bin_code :=
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
      Some [ins32]
  | SUB   => Some [bpf_alu32_to_thumb_reg_comm SUB_R_OP dst src]
  | MUL   =>
    let ins_lo  := encode_arm32 (int_of_breg dst) MUL_OP 0 4 in
    let ins_hi0 := encode_arm32 (int_of_breg dst) (int_of_ireg src) 8 4 in
    let ins_hi  := encode_arm32 (Int.repr 0xf) ins_hi0 12 4 in
    let ins32   := encode_arm32 ins_hi ins_lo 16 16 in
      Some [ins32]
  | DIV   => None

  | OR    => Some [bpf_alu32_to_thumb_reg_comm ORR_R_OP dst src]
  | AND   => Some [bpf_alu32_to_thumb_reg_comm AND_R_OP dst src]
  | LSH   => None
  | RSH   => None
  | NEG   => None
  | MOD   => None
  | XOR   => Some [bpf_alu32_to_thumb_reg_comm EOR_R_OP dst src]
  | MOV   =>
    (**r optimization: for `mov ri ri`, we generate nothing *)
    if reg_ireg_eqb dst src then
      Some []
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
        Some [ins32]
  | ARSH  => None
  end.

(**r move imm32 low16-bit to ireg *)

Definition mov_int_to_movwt (i: int) (r: ireg) (op: int): int :=
  let lo_imm8   := decode_arm32 i 0  8 in
  let lo_imm3   := decode_arm32 i 8  3 in
  let lo_i      := decode_arm32 i 11 1 in
  let lo_imm4   := decode_arm32 i 12 4 in
(**r - encoding T3
MOVW Rd, #imm16 (= imm4:i:imm3:imm8)

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 0|i|1 0|0|1|0 0| imm4  |   |0| imm3|  Rd   |  imm8         |
 --------------------------------    -------------------------------- *)
  let movw_lo_0 := encode_arm32 lo_imm4 op        0  4 in
  let movw_lo   := encode_arm32 lo_i    movw_lo_0 10 1 in

  let movw_hi_0 := encode_arm32 (int_of_ireg r) lo_imm8 8 4 in
  let movw_hi   := encode_arm32 lo_imm3 movw_hi_0 12 3 in
    encode_arm32 movw_hi movw_lo 16 16.

(**r - encoding T1
MOVT Rd, #imm16 (= imm4:i:imm3:imm8)

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 0|i|1 0|1|1|0|0| imm4  |   |0| imm3|  Rd   |  imm8         |
 --------------------------------    -------------------------------- *)

Definition bpf_alu32_to_thumb_imm_comm (op: int) (alu_op: aluOp) (dst: breg) (imm32: int): option bin_code :=
  if (Int.cmpu Cle Int.zero imm32) && (Int.cmpu Cle imm32 (Int.repr 255)) then (**r 0 <= imm32 <= 255 *)
    let ins_lo    := encode_arm32 (int_of_breg dst) op 0 4 in
    let ins_hi    := encode_arm32 (int_of_breg dst) imm32 8 4 in
    let ins32     := encode_arm32 ins_hi ins_lo 16 16 in
      Some [ins32]
  else
    let lo_32 := decode_arm32 imm32 0 16 in
    let hi_32 := decode_arm32 imm32 16 16 in
      if Int.eq lo_32 imm32 then (**r optimization: if high_16 = 0 then only add `movw` *)
        match bpf_alu32_to_thumb_reg alu_op dst IR11 with
        | Some l => Some ((mov_int_to_movwt lo_32 IR11 MOVW_OP) :: l)
        | None => None
        end
      else (**r optimization: if high_16 <> 0 then add`movt + movw` *)
        match bpf_alu32_to_thumb_reg alu_op dst IR11 with
        | Some l =>
          (**r adding movw movt: must firstly w then t *)
          Some ((mov_int_to_movwt lo_32 IR11 MOVW_OP) :: (mov_int_to_movwt hi_32 IR11 MOVT_OP) :: l)
        | None => None
        end.

Definition bpf_alu32_to_thumb_imm_shift_comm (op: int) (dst: breg) (imm32: int): option bin_code :=
  (**r CompCert doesn't have lsh_imm, so we do `mov + lsh_reg` *)
  (**r BPF verifier should guarantee 0 <= imm32 < 32 for lsh_imm *)
  if (Int.cmpu Cle Int.zero imm32) && (Int.cmpu Clt imm32 (Int.repr 32)) then
    (**r construct: lsl/lsr/asr Rd Rn Rm *)
    let ins_lo  := encode_arm32 (int_of_breg dst) op 0 4 in
    let ins_hi0 := encode_arm32 (int_of_breg dst) (int_of_ireg IR11) 8 4 in
    let ins_hi  := encode_arm32 (Int.repr 0xf) ins_hi0 12 4 in
    let ins32   := encode_arm32 ins_hi ins_lo 16 16 in
      Some [mov_int_to_movwt imm32 IR11 MOVW_OP; ins32]
  else
    None.

Definition bpf_alu32_to_thumb_imm (op: aluOp) (dst: breg) (imm32: int): option bin_code :=
  match op with
  | ADD   => bpf_alu32_to_thumb_imm_comm ADD_I_OP ADD dst imm32
  | SUB   => bpf_alu32_to_thumb_imm_comm SUB_I_OP SUB dst imm32
  | MUL   => (**r CompCert doesn't have mul_imm, so we do `mov + mul_reg` *)
    let lo_32 := decode_arm32 imm32 0 16 in
    let hi_32 := decode_arm32 imm32 16 16 in
      if Int.eq lo_32 imm32 then (**r optimization: if high_16 = 0 then only add `movw` *)
        match bpf_alu32_to_thumb_reg MUL dst IR11 with
        | Some l => Some ((mov_int_to_movwt lo_32 IR11 MOVW_OP) :: l)
        | None => None
        end
      else (**r optimization: if high_16 <> 0 then add`movt + movw` *)
        (**r adding movw movt: must firstly w then t *)
        match bpf_alu32_to_thumb_reg MUL dst IR11 with
        | Some l => Some ((mov_int_to_movwt lo_32 IR11 MOVW_OP) ::
              (mov_int_to_movwt hi_32 IR11 MOVT_OP) :: l)
        | None => None
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
          Some [mov_int_to_movwt lo_32 IR11 MOVW_OP; ins32]
        else (**r optimization: if high_16 <> 0 then add`movt + movw` *)
          (**r adding movw movt: must firstly w then t *)
          Some [mov_int_to_movwt lo_32 IR11 MOVW_OP; mov_int_to_movwt hi_32 IR11 MOVT_OP; ins32]

  | OR    => bpf_alu32_to_thumb_imm_comm ORR_I_OP OR  dst imm32
  | AND   => bpf_alu32_to_thumb_imm_comm AND_I_OP AND dst imm32
  | LSH   => bpf_alu32_to_thumb_imm_shift_comm LSL_R_OP dst imm32
  | RSH   => bpf_alu32_to_thumb_imm_shift_comm LSR_R_OP dst imm32
  | NEG   =>
    let ins_lo    := encode_arm32 (int_of_ireg IR11) RSB_I_OP 0 4 in (**r dst = 0 - IR11 *)
    let ins_hi    := encode_arm32 (int_of_breg dst) Int.zero 8 4 in
    let ins32     := encode_arm32 ins_hi ins_lo 16 16 in
    let lo_32 := decode_arm32 imm32 0 16 in
    let hi_32 := decode_arm32 imm32 16 16 in
      if Int.eq lo_32 imm32 then (**r optimization: if high_16 = 0 then only add `movw` *)
        Some ((mov_int_to_movwt lo_32 IR11 MOVW_OP) :: [ins32])
      else (**r optimization: if high_16 <> 0 then add`movt + movw` *)
        (**r adding movw movt: must firstly w then t *)
        Some ((mov_int_to_movwt lo_32 IR11 MOVW_OP) ::
              (mov_int_to_movwt hi_32 IR11 MOVT_OP) :: [ins32])
  | MOD   => None
  | XOR   => bpf_alu32_to_thumb_imm_comm EOR_I_OP XOR dst imm32
  | MOV   =>
    let lo_32 := decode_arm32 imm32 0 16 in
    let hi_32 := decode_arm32 imm32 16 16 in
      if Int.eq lo_32 imm32 then (**r optimization: if high_16 = 0 then only add `movw` *)
        Some [mov_int_to_movwt lo_32 (ireg_of_breg dst) MOVW_OP]
      else (**r optimization: if high_16 <> 0 then add`movt + movw` *)
        (**r adding movw movt: must firstly w then t *)
        Some [mov_int_to_movwt lo_32 (ireg_of_breg dst) MOVW_OP;
          (mov_int_to_movwt hi_32 (ireg_of_breg dst) MOVT_OP)]
  | ARSH  => bpf_alu32_to_thumb_imm_shift_comm ASR_R_OP dst imm32
  end.


Definition jit_one (op:aluOp) (dst: breg) (src: breg+imm) (ld_set st_set: listset):
  option (bin_code * listset * listset) :=
  match src with
  | inl r =>
    let '(l1, ld_set1, st_set1) := jit_call_save_reg dst r ld_set st_set in
      match bpf_alu32_to_thumb_reg op dst (ireg_of_breg r) with
      | None => None
      | Some l2 => Some (l1 ++ l2, ld_set1, st_set1)
      end
  | inr i =>
    let '(l1, ld_set1, st_set1) := jit_call_save_imm dst ld_set st_set in
      match bpf_alu32_to_thumb_imm op dst i with
      | None => None
      | Some l2 => Some (l1 ++ l2, ld_set1, st_set1)
      end
  end.

Fixpoint jit_sequence (l: bpf_code) (ld_set st_set: listset):
  option (bin_code * listset * listset) :=
  match l with
  | [] => Some ([], ld_set, st_set)
  | hd :: tl =>
    match hd with
    | Palu32 op dst src =>
      match jit_one op dst src ld_set st_set with
      | None => None
      | Some (l1, ld1, st1) =>
        match jit_sequence tl ld1 st1 with
        | None => None
        | Some (l2, ld2, st2) => Some (l1++l2, ld2, st2)
        end
      end
    | _ => None
    end
  end.


Definition jit_alu32_thumb_pc_add (imm32: int): option bin_code :=
  if (Int.cmpu Cle Int.zero imm32) && (Int.cmpu Cle imm32 (Int.repr 255)) then (**r 0 <= imm32 <= 255 *)
    let ins_lo    := encode_arm32 (Int.repr 11) ADD_I_OP 0 4 in
    let ins_hi    := encode_arm32 (Int.repr 11) imm32 8 4 in
    let ins32     := encode_arm32 ins_hi ins_lo 16 16 in
      Some [ins32]
  else
    None.

Definition jit_alu32_thumb_pc (num: nat): option bin_code :=
  (**r TODO: 2023-06-13
      ldr r11, [r12, #44]
      add r11, (thumb_len st)
      str r11, [r12, #44] *)
  match jit_alu32_thumb_pc_add (Int.repr (Z.of_nat num)) with
  | None => None
  | Some l =>
    let l_ldr := jit_alu32_thumb_mem_template_jit LDR_I_OP
      (Int.repr 11) (int_of_ireg IR12) (Int.repr 44) in
    let l_str := jit_alu32_thumb_mem_template_jit STR_I_OP
      (Int.repr 11) (int_of_ireg IR12) (Int.repr 44) in
      Some ([l_ldr] ++ l ++ [l_str])
  end.

(** * Store Stage: Store selected arm32 registers into corresponding BPF registers *)

Fixpoint jit_alu32_thumb_store (st_set: listset): bin_code :=
  match st_set with
  | [] => []
  | hd :: tl =>
    let l_str := jit_alu32_thumb_mem_template_jit STR_I_OP (int_of_breg hd) (int_of_ireg IR12)
                    (Int.mul (int_of_breg hd) (Int.repr 4)) in
      [l_str] ++ (jit_alu32_thumb_store tl)
  end.

(** * Reset Stage: recover the initial value of selected arm32 registers *)

(** @input
  * @r   : pop register r from the stack

  * @output
  * @ins :  binary format of `ldr r [sp, #+ofs]` where we use `ldr` to implement `pop`
  *)

Fixpoint jit_alu32_thumb_reset1 (ld_set: listset): bin_code :=
  match ld_set with
  | [] => []
  | hd :: tl =>
    (**r determine if we should do calling_convention, depends on r [4, 11] where 11 must be done because of the pre Stage *)
    if (Int.ltu (Int.repr 3) (int_of_breg hd)) && (Int.ltu (int_of_breg hd) (Int.repr 11)) then
      let l_ldr := jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg hd) (int_of_ireg IR13)
                      (Int.mul (int_of_breg hd) (Int.repr 4)) in
      [l_ldr] ++ (jit_alu32_thumb_reset1 tl)
    else
      jit_alu32_thumb_reset1 tl
  end.

Definition jit_alu32_thumb_reset (ld_set: listset): bin_code :=
  let l_ldr := jit_alu32_thumb_mem_template_jit LDR_I_OP (Int.repr 11) (int_of_ireg IR13) (Int.repr 44) in
    [l_ldr] ++ jit_alu32_thumb_reset1 ld_set.

(** Post: LDR SP [SP, #+0]; BX LR *)

Definition jit_alu32_post: bin_code :=
  (**r LDR SP [SP, #+0] *)
  let l_ldr := jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_ireg SP) (int_of_ireg SP) Int.zero in
  (**r BX LR *)
  let ins_rm   := encode_arm32 (int_of_ireg RA) BX_OP 3 4 in
  let ins32    := encode_arm32 ins_rm NOP_OP 16 16 in
    [l_ldr] ++ [ins32].

(** * Jit Procedure *)

Definition jit_alu32_aux (l: bpf_code): option bin_code :=
  match jit_sequence l [] [] with
  | None => None
  | Some (cl, ld_set, st_set) =>
    match cl with
    | [] => None (**r we don't want this case, wher should we put this check? *)
    | _ =>
      match jit_alu32_thumb_pc (List.length l) with
      | None => None
      | Some l_pc =>
        Some (cl ++ l_pc ++ (jit_alu32_thumb_store st_set) ++
              (jit_alu32_thumb_reset ld_set))
      end
    end
  end.

Definition jit_alu32 (l: bpf_code): option bin_code :=
  match jit_alu32_aux l with
  | None => None
  | Some bl => Some (jit_alu32_pre ++ (bl ++ jit_alu32_post))
  end.

Close Scope asm.
Close Scope bool_scope.
Close Scope Z_scope.