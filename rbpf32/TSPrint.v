From compcert Require Import Integers AST Ctypes.
From Coq Require Import ZArith Ascii String HexString List.

From bpf.rbpf32 Require Import TSSyntax.

Import ListNotations.

(** * rBPF Print Module *)

(** This file is used to print rBPF instructions from syntax *)

Definition string_of_reg (r: breg): string :=
  match r with
  | R0 => "r0"
  | R1 => "r1"
  | R2 => "r2"
  | R3 => "r3"
  | R4 => "r4"
  | R5 => "r5"
  | R6 => "r6"
  | R7 => "r7"
  | R8 => "r8"
  | R9 => "r9"
  | R10 => "r10"
  end.

Definition string_of_byte (i: byte): string := of_Z (Byte.unsigned i).

Definition string_of_int_unsigned (i: int): string := of_Z (Int.unsigned i).

Definition string_of_int_signed (i: int): string := of_Z (Int.signed i).
(*
Definition string_of_ptrofs (i: off): string := of_Z (Int.signed (Ptrofs.to_int i)). *)
Definition string_of_ptrofs (i: int): string := of_Z (Int.signed i).

Definition string_of_pos (i: positive): string := of_Z (Z.of_nat (Pos.to_nat i)).

Definition print_reg_imm (ri: breg+imm): string :=
  match ri with
  | inl r => string_of_reg r
  | inr i => string_of_int_signed i
  end.

Definition string_of_signedness (s: signedness): string :=
  match s with
  | Signed => "(signed)"
  | Unsigned => ""
  end.

Definition string_of_sizeOp (sz: sizeOp): string :=
  match sz with
  | Word      => "32"
  | HalfWord  => "16"
  | Byte      => "8"
  end.

Definition print_rBPF_instruction (ins: instruction): string :=
  match ins with
  | Pload sz dst src ofs =>
    "Load" ++ (string_of_sizeOp sz) ++ " " ++
    (string_of_reg dst) ++ " " ++ (string_of_reg src) ++ " " ++ (string_of_ptrofs ofs)
  | Pstore sz dst src ofs =>
    "Store" ++ (string_of_sizeOp sz) ++ " " ++
    (string_of_reg dst) ++ " " ++ (print_reg_imm src) ++ " " ++ (string_of_ptrofs ofs)
  | Palu32 op dst src =>
    let dst_string := string_of_reg dst in
    let src_string := print_reg_imm src in
      match op with
      | ADD   => dst_string ++ " +=" ++ " " ++ src_string
      | SUB   => dst_string ++ " -=" ++ " " ++ src_string
      | MUL   => dst_string ++ " *=" ++ " " ++ src_string
      | DIV   => dst_string ++ " /=" ++ " " ++ src_string
      | OR    => dst_string ++ " |=" ++ " " ++ src_string
      | AND   => dst_string ++ " &=" ++ " " ++ src_string
      | LSH   => dst_string ++ " <<=" ++ " " ++ src_string
      | RSH   => dst_string ++ " >>=" ++ " " ++ src_string
      | NEG   => dst_string ++ " =" ++ " ~" ++ src_string
      | MOD   => dst_string ++ " %=" ++ " " ++ src_string
      | XOR   => dst_string ++ " ^=" ++ " " ++ src_string
      | MOV   => dst_string ++ " =" ++ " " ++ src_string
      | ARSH  => dst_string ++ " >>=" ++ " (signed)" ++ src_string
      end
  | Pjmp lbl => "JA " ++ (string_of_ptrofs lbl)
  | Pjmpcmp op dst src lbl =>
    let dst_string := string_of_reg dst in
    let src_string := print_reg_imm src in
    let ofs_string := string_of_ptrofs lbl in
      match op with
      | EQ    => "if " ++ dst_string ++ " == " ++ src_string ++ " goto " ++ ofs_string
      | SET   => "if " ++ dst_string ++ " & " ++ src_string ++ " goto " ++ ofs_string
      | NE    => "if " ++ dst_string ++ " != " ++ src_string ++ " goto " ++ ofs_string
      | GT s  => "if " ++ (string_of_signedness s) ++ dst_string ++ " > "  ++
                   (string_of_signedness s) ++ src_string ++ " goto " ++ ofs_string
      | GE s  => "if " ++ (string_of_signedness s) ++ dst_string ++ " >= " ++
                   (string_of_signedness s) ++ src_string ++ " goto " ++ ofs_string
      | LT s  => "if " ++ (string_of_signedness s) ++ dst_string ++ " < "  ++
                   (string_of_signedness s) ++ src_string ++ " goto " ++ ofs_string
      | LE s  => "if " ++ (string_of_signedness s) ++ dst_string ++ " <= " ++
                   (string_of_signedness s) ++ src_string ++ " goto " ++ ofs_string
      end
  | Pret => "exit"
  | _ => ""
  end.

Fixpoint print_rBPF_prog_aux (pc: nat) (l: list instruction): list string :=
  match l with
  | [] => []
  | hd :: tl =>
    let ins_string := print_rBPF_instruction hd in
      List.app [((of_nat pc) ++ ": " ++ ins_string)%string] (print_rBPF_prog_aux (S pc) tl)
  end.

Definition print_rBPF_prog (l: list instruction): list string :=
  print_rBPF_prog_aux 0 l.
