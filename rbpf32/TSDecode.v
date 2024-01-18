From compcert.lib Require Import Integers Coqlib Maps.
From compcert.cfrontend Require Import Ctypes.

From Coq Require Import ZArith List.
Import ListNotations.

From bpf.comm Require Import BinrBPF.
From bpf.rbpf32 Require Import TSSyntax.

Open Scope nat_scope.

Definition get_instruction_alu32_imm (rd: breg) (i: imm) (op: nat): option instruction :=
  match op with
  (* ALU32_imm *)
  | 0x04 => Some (Palu32 ADD  rd (inr i))
  | 0x14 => Some (Palu32 SUB  rd (inr i))
  | 0x24 => Some (Palu32 MUL  rd (inr i))
  | 0x34 => Some (Palu32 DIV  rd (inr i))
  | 0x44 => Some (Palu32 OR   rd (inr i))
  | 0x54 => Some (Palu32 AND  rd (inr i))
  | 0x64 => Some (Palu32 LSH  rd (inr i))
  | 0x74 => Some (Palu32 RSH  rd (inr i))
  | 0x84 => Some (Palu32 NEG  rd (inl rd))
  | 0x94 => Some (Palu32 MOD  rd (inr i))
  | 0xa4 => Some (Palu32 XOR  rd (inr i))
  | 0xb4 => Some (Palu32 MOV  rd (inr i))
  | 0xc4 => Some (Palu32 ARSH rd (inr i))
  | _    => None
  end.

Definition get_instruction_alu32_reg (rd rs: breg) (op: nat): option instruction :=
  match op with
  (*ALU32*)
  | 0x0c => Some (Palu32 ADD  rd (inl rs))
  | 0x1c => Some (Palu32 SUB  rd (inl rs))
  | 0x2c => Some (Palu32 MUL  rd (inl rs))
  | 0x3c => Some (Palu32 DIV  rd (inl rs))
  | 0x4c => Some (Palu32 OR   rd (inl rs))
  | 0x5c => Some (Palu32 AND  rd (inl rs))
  | 0x6c => Some (Palu32 LSH  rd (inl rs))
  | 0x7c => Some (Palu32 RSH  rd (inl rs))
  | 0x9c => Some (Palu32 MOD  rd (inl rs))
  | 0xac => Some (Palu32 XOR  rd (inl rs))
  | 0xbc => Some (Palu32 MOV  rd (inl rs))
  | 0xcc => Some (Palu32 ARSH rd (inl rs))
  | _    => None
  end.

Definition get_instruction_ldx (rd rs: breg) (ofs: off) (op: nat): option instruction :=
  match Nat.land op 255 with
  | 0x61 => Some (Pload Word     rd rs ofs)
  | 0x69 => Some (Pload HalfWord rd rs ofs)
  | 0x71 => Some (Pload Byte     rd rs ofs)
  | _    => None
  end.

Definition get_instruction_st (rd: breg) (ofs: off) (i: int) (op: nat): option instruction :=
  match Nat.land op 255 with
  | 0x62 => Some (Pstore  Word     rd (inr i)  ofs)
  | 0x6a => Some (Pstore  HalfWord rd (inr i)  ofs)
  | 0x72 => Some (Pstore  Byte     rd (inr i)  ofs)
  | _    => None
  end.

Definition get_instruction_stx (rd rs: breg) (ofs: off) (op: nat): option instruction :=
  match Nat.land op 255 with
  | 0x63 => Some (Pstore  Word     rd (inl rs) ofs)
  | 0x6b => Some (Pstore  HalfWord rd (inl rs) ofs)
  | 0x73 => Some (Pstore  Byte     rd (inl rs) ofs)
  | _    => None
  end.

Definition get_instruction_branch_imm (rd: breg) (ofs: off) (i: imm) (op: nat): option instruction :=
  match op with
  | 0x05 => Some (Pjmp ofs)
  | 0x15 => Some (Pjmpcmp  EQ           rd (inr i)  ofs)
  | 0x25 => Some (Pjmpcmp (GT Unsigned) rd (inr i)  ofs)
  | 0x35 => Some (Pjmpcmp (GE Unsigned) rd (inr i)  ofs)
  | 0xa5 => Some (Pjmpcmp (LT Unsigned) rd (inr i)  ofs)
  | 0xb5 => Some (Pjmpcmp (LE Unsigned) rd (inr i)  ofs)
  | 0x45 => Some (Pjmpcmp  SET          rd (inr i)  ofs)
  | 0x55 => Some (Pjmpcmp  NE           rd (inr i)  ofs)
  | 0x65 => Some (Pjmpcmp (GT Signed)   rd (inr i)  ofs)
  | 0x75 => Some (Pjmpcmp (GE Signed)   rd (inr i)  ofs)
  | 0xc5 => Some (Pjmpcmp (LT Signed)   rd (inr i)  ofs)
  | 0xd5 => Some (Pjmpcmp (LE Signed)   rd (inr i)  ofs)
(*
  | 0x85 => Pcall i *)
  | 0x95 => Some Pret

  | _    => None
  end.

Definition get_instruction_branch_reg (rd rs: breg) (ofs: off) (op: nat): option instruction :=
  match op with
  | 0x1d => Some (Pjmpcmp  EQ           rd (inl rs) ofs)
  | 0x2d => Some (Pjmpcmp (GT Unsigned) rd (inl rs) ofs)
  | 0x3d => Some (Pjmpcmp (GE Unsigned) rd (inl rs) ofs)
  | 0xad => Some (Pjmpcmp (LT Unsigned) rd (inl rs) ofs)
  | 0xbd => Some (Pjmpcmp (LE Unsigned) rd (inl rs) ofs)
  | 0x4d => Some (Pjmpcmp  SET          rd (inl rs) ofs)
  | 0x5d => Some (Pjmpcmp  NE           rd (inl rs) ofs)
  | 0x6d => Some (Pjmpcmp (GT Signed)   rd (inl rs) ofs)
  | 0x7d => Some (Pjmpcmp (GE Signed)   rd (inl rs) ofs)
  | 0xcd => Some (Pjmpcmp (LT Signed)   rd (inl rs) ofs)
  | 0xdd => Some (Pjmpcmp (LE Signed)   rd (inl rs) ofs)
  | _    => None
  end.

Definition z_to_breg (z:Z): option breg :=
  if (Z.eqb z 0) then
    Some R0
  else if (Z.eqb z 1) then
    Some R1
  else if (Z.eqb z 2) then
    Some R2
  else if (Z.eqb z 3) then
    Some R3
  else if (Z.eqb z 4) then
    Some R4
  else if (Z.eqb z 5) then
    Some R5
  else if (Z.eqb z 6) then
    Some R6
  else if (Z.eqb z 7) then
    Some R7
  else if (Z.eqb z 8) then
    Some R8
  else if (Z.eqb z 9) then
    Some R9
  else if (Z.eqb z 10) then
    Some R10
  else
    None.

Definition int64_to_dst_breg (ins: int64): option breg := z_to_breg (get_dst ins).

Definition int64_to_src_breg (ins: int64): option breg := z_to_breg (get_src ins).

Definition decode_ind (ins: int64): option instruction :=
  let opcode := get_opcode ins in
    match int64_to_dst_breg ins with
    | None => None
    | Some dst =>
      let opc := Nat.land opcode 0x07 in (**r masking operation *)
      let n_ofs    := get_offset ins in
      let n_imm    := get_immediate ins in
        match opc with
        | 0x04 => (* ALU32 *)
          if Int.eq Int.zero (Int.and (Int.repr (Z.of_nat opcode)) (Int.repr 8)) then
            get_instruction_alu32_imm dst n_imm opcode
          else
            match int64_to_src_breg ins with
            | None => None
            | Some src => get_instruction_alu32_reg dst src opcode
            end
        | 0x05 => (* Branch *)
          if Int.eq Int.zero (Int.and (Int.repr (Z.of_nat opcode)) (Int.repr 8)) then
            get_instruction_branch_imm dst n_ofs n_imm opcode
          else
            match int64_to_src_breg ins with
            | None => None
            | Some src => get_instruction_branch_reg dst src n_ofs opcode
            end
        | 0x01 => (* Mem_ld_reg *)
          match int64_to_src_breg ins with
          | None => None
          | Some src => get_instruction_ldx dst src n_ofs opcode
          end
        | 0x02 => (* Mem_st_imm *) get_instruction_st dst n_ofs n_imm opcode
        | 0x03 => (* Mem_st_reg *)
          match int64_to_src_breg ins with
          | None => None
          | Some src => get_instruction_stx dst src n_ofs opcode
          end
        | _    => None
        end
    end.

Fixpoint decode_prog_aux (fuel pc: nat) (l: list int64): list instruction :=
  match fuel with
  | O => []
  | S n =>
    match List.nth_error l pc with
    | Some i =>
      match decode_ind i with
      | Some ins => [ins] ++ (decode_prog_aux n (S pc) l)
      | None => []
      end
    | None => []
    end
  end.

Definition decode_prog (l: list int64) (len: nat): list instruction :=
  decode_prog_aux len 0 l.

Definition find_instr (pos: nat) (c: code): option instruction :=
  match List.nth_error c pos with
  | Some ins => decode_ind ins
  | None => None
  end.