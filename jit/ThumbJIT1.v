From compcert Require Import Integers.
From compcert.arm Require Import AsmSyntax BinSyntax BinDecode.

From bpf.comm Require Import Flag BinrBPF ListAsArray Regs.
From bpf.rbpf32 Require Import TSSyntax TSDecode JITConfig.
From bpf.jit Require Import Arm32Reg ThumbInsOp ListSetRefinement ThumbJIT.

From Coq Require Import List ZArith Arith String.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope asm.

(**r Target: replace listset with record which can be translated into an array in C,
  The order of store and reloading-related instructions are fixed now
 *)


(** * Jitted Code: from BPF alu32 to thumb alu *)
Definition jit_call_save_add_refine (r: breg) (ls: listset_regmap): bin_code :=
  if eval_listset_regmap r ls then
    []
  else
    (**r determine if we should do calling_convention, depends on r [4, 11] *) (*
    if (Int.ltu (Int.repr 3) (int_of_reg r)) && (Int.ltu (int_of_reg r) (int_of_ireg IR12)) then *)
    let ldr_ins := jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg r) (int_of_ireg IR12)
                  (Int.mul (int_of_breg r) (Int.repr 4)) in
      if (Int.ltu (Int.repr 3) (int_of_breg r)) && (Int.ltu (int_of_breg r) (int_of_ireg IR12)) then
        let str_ins := jit_alu32_thumb_mem_template_jit STR_I_OP (int_of_breg r) (int_of_ireg SP)
                      (Int.mul (int_of_breg r) (Int.repr 4)) in
          [str_ins; ldr_ins]
        else
          [ldr_ins].

Definition jit_call_save_reg_refine (dst src: breg) (ld_set st_set: listset_regmap): bin_code * listset_regmap * listset_regmap :=
  let l1 := jit_call_save_add_refine dst ld_set in
  let ld_set1 := listset_add_regmap dst ld_set in
  let st_set1 := listset_add_regmap dst st_set in

  let l2 := jit_call_save_add_refine src ld_set1 in
  let ld_set2 := listset_add_regmap src ld_set1 in
    (l1 ++ l2, ld_set2, st_set1).

Definition jit_call_save_imm_refine (dst: breg) (ld_set st_set: listset_regmap): bin_code * listset_regmap * listset_regmap :=
  let l1 := jit_call_save_add_refine dst ld_set in
    (l1, listset_add_regmap dst ld_set, listset_add_regmap dst st_set).

Definition jit_one_refine (op:aluOp) (dst: breg) (src: breg+imm) (ld_set st_set: listset_regmap):
  option (bin_code * listset_regmap * listset_regmap) :=
  match src with
  | inl r =>
    let '(l1, ld_set1, st_set1) := jit_call_save_reg_refine dst r ld_set st_set in
      match bpf_alu32_to_thumb_reg op dst (ireg_of_breg r) with
      | None => None
      | Some l2 => Some (l1 ++ l2, ld_set1, st_set1)
      end
  | inr i =>
    let '(l1, ld_set1, st_set1) := jit_call_save_imm_refine dst ld_set st_set in
      match bpf_alu32_to_thumb_imm op dst i with
      | None => None
      | Some l2 => Some (l1 ++ l2, ld_set1, st_set1)
      end
  end.

Fixpoint jit_sequence_refine (l: bpf_code) (ld_set st_set: listset_regmap):
  option (bin_code * listset_regmap * listset_regmap) :=
  match l with
  | [] => Some ([], ld_set, st_set)
  | hd :: tl =>
    match hd with
    | Palu32 op dst src =>
      match jit_one_refine op dst src ld_set st_set with
      | None => None
      | Some (l1, ld1, st1) =>
        match jit_sequence_refine tl ld1 st1 with
        | None => None
        | Some (l2, ld2, st2) => Some (l1++l2, ld2, st2)
        end
      end
    | _ => None
    end
  end.

(** * Store Stage: Store selected arm32 registers into corresponding BPF registers *)

Definition jit_alu32_thumb_upd_store (r: breg) (st_set: listset_regmap): bin_code :=
  if eval_listset_regmap r st_set then
    [jit_alu32_thumb_mem_template_jit STR_I_OP (int_of_breg r) (int_of_ireg IR12)
                    (Int.mul (int_of_breg r) (Int.repr 4))]
  else
    [].

Definition jit_alu32_thumb_store_refine (st_set: listset_regmap): bin_code :=
  let ins0 := jit_alu32_thumb_upd_store R0 st_set in
  let ins1 := jit_alu32_thumb_upd_store R1 st_set in
  let ins2 := jit_alu32_thumb_upd_store R2 st_set in
  let ins3 := jit_alu32_thumb_upd_store R3 st_set in
  let ins4 := jit_alu32_thumb_upd_store R4 st_set in
  let ins5 := jit_alu32_thumb_upd_store R5 st_set in
  let ins6 := jit_alu32_thumb_upd_store R6 st_set in
  let ins7 := jit_alu32_thumb_upd_store R7 st_set in
  let ins8 := jit_alu32_thumb_upd_store R8 st_set in
  let ins9 := jit_alu32_thumb_upd_store R9 st_set in
  let ins10 := jit_alu32_thumb_upd_store R10 st_set in
    ins0 ++ ins1 ++ ins2 ++ ins3 ++ ins4 ++ ins5 ++ ins6 ++ ins7 ++ ins8 ++ ins9 ++ ins10.

(** * Reset Stage: recover the initial value of selected arm32 registers *)

Definition jit_alu32_thumb_upd_reset (r: breg) (ld_set: listset_regmap): bin_code :=
  if eval_listset_regmap r ld_set then
    [jit_alu32_thumb_mem_template_jit LDR_I_OP (int_of_breg r) (int_of_ireg IR13)
                      (Int.mul (int_of_breg r) (Int.repr 4))]
  else
    [].

Definition jit_alu32_thumb_reset1_refine (ld_set: listset_regmap): bin_code :=
  let ins4 := jit_alu32_thumb_upd_reset R4 ld_set in
  let ins5 := jit_alu32_thumb_upd_reset R5 ld_set in
  let ins6 := jit_alu32_thumb_upd_reset R6 ld_set in
  let ins7 := jit_alu32_thumb_upd_reset R7 ld_set in
  let ins8 := jit_alu32_thumb_upd_reset R8 ld_set in
  let ins9 := jit_alu32_thumb_upd_reset R9 ld_set in
  let ins10 := jit_alu32_thumb_upd_reset R10 ld_set in
    ins4 ++ ins5 ++ ins6 ++ ins7 ++ ins8 ++ ins9 ++ ins10.

Definition jit_alu32_thumb_reset_refine (ld_set: listset_regmap): bin_code :=
  let l_ldr := jit_alu32_thumb_mem_template_jit LDR_I_OP (Int.repr 11) (int_of_ireg IR13) (Int.repr 44) in
    [l_ldr] ++ jit_alu32_thumb_reset1_refine ld_set.

(** * Jit Procedure *)

Definition jit_alu32_aux_refine (l: bpf_code): option bin_code :=
  match jit_sequence_refine l init_listset_regmap init_listset_regmap with
  | None => None
  | Some (cl, ld_set, st_set) =>
    match cl with
    | [] => None (**r we don't want this case, wher should we put this check? *)
    | _ =>
      match jit_alu32_thumb_pc (List.length l) with
      | None => None
      | Some l_pc =>
        Some (cl ++ l_pc ++ (jit_alu32_thumb_store_refine st_set) ++
              (jit_alu32_thumb_reset_refine ld_set))
      end
    end
  end.

Definition jit_alu32_refine (l: bpf_code): option bin_code :=
  match jit_alu32_aux_refine l with
  | None => None
  | Some bl => Some (jit_alu32_pre ++ (bl ++ jit_alu32_post))
  end.

Close Scope asm.
Close Scope bool_scope.
Close Scope Z_scope.