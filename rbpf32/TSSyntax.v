From compcert.lib Require Import Integers Coqlib Maps.
From compcert.common Require Import AST Values Globalenvs Memory Events Smallstep.
From compcert.cfrontend Require Import Ctypes.

From Coq Require Import ZArith List FSetList ListSet.

Open Scope Z_scope.
Import ListNotations.

(** * Abstract syntax *)

(** We model the following registers of the eBPF architecture. *)

Inductive breg: Type := R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 (*| RA is actually R9 *).

Definition listset := set breg.

(*
Definition breg_eqp (r1 r2: breg): Prop := r1 = r2.

Lemma equiv_breg_eqp: Equivalence breg_eqp.
Proof.
  unfold breg_eqp.
  constructor; auto.
  unfold Transitive.
  intros.
  rewrite H. auto.
Qed. *)

Definition z_of_breg (i: breg): Z :=
  match i with
  | R0 => 0
  | R1 => 1
  | R2 => 2
  | R3 => 3
  | R4 => 4
  | R5 => 5
  | R6 => 6
  | R7 => 7
  | R8 => 8
  | R9 => 9
  | R10 => 10
  end.

Definition breg_ltp (r1 r2: breg): Prop := Z.lt (z_of_breg r1) (z_of_breg r2).

Lemma breg_lt_strorder : StrictOrder breg_ltp.
Proof.
  unfold breg_ltp; constructor.
  - unfold Irreflexive.
    unfold Reflexive, complement.
    intros.
    lia.
  - unfold Transitive.
    intros.
    lia.
Qed.

Lemma breg_lt_compat: Proper (@eq breg ==> @eq breg ==> iff) breg_ltp.
Proof.
  unfold breg_ltp; constructor; intros.
  - subst. auto.
  - subst. auto.
Qed.

Definition breg_compare (r1 r2: breg): Datatypes.comparison :=
  Z.compare (z_of_breg r1) (z_of_breg r2).

Lemma z_of_breg_eq_iff:
  forall x y, z_of_breg x = z_of_breg y <-> x = y.
Proof.
  split; intros.
  - destruct x; destruct y; (try reflexivity); inversion H.
  - subst; auto.
Qed.

Lemma z_of_breg_neq_iff:
  forall x y, z_of_breg x <> z_of_breg y <-> x <> y.
Proof.
  split; intros.
  - intro HF.
    rewrite <- z_of_breg_eq_iff in HF.
    rewrite HF in H.
    apply H; auto.
  - intro HF.
    rewrite z_of_breg_eq_iff in HF.
    rewrite HF in H.
    apply H; auto.
Qed.

Lemma breg_compare_spec : forall x y : breg,
  CompareSpec (eq x y) (breg_ltp x y) (breg_ltp y x) (breg_compare x y).
Proof.
  unfold breg_ltp.
  intros.
  destruct breg_compare eqn: Hcmp; unfold breg_compare in Hcmp; constructor.
  - apply Z.compare_eq in Hcmp.
    rewrite <- z_of_breg_eq_iff; auto.
  - rewrite Z.compare_lt_iff in Hcmp; auto.
  - rewrite Z.compare_gt_iff in Hcmp; auto.
Qed.

Lemma breg_eq: forall (x y: breg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Module BregOrderListSetType <: Orders.OrderedType.
  Definition t  := breg.
  Definition eq := @eq breg.
  Definition eq_equiv := @eq_equivalence breg.
  Definition lt := breg_ltp.
  Definition lt_strorder := breg_lt_strorder.
  Definition lt_compat := breg_lt_compat.
  Definition compare := breg_compare.
  Definition compare_spec := breg_compare_spec.
  Definition eq_dec := breg_eq.
End BregOrderListSetType.

Module BregOrderListSet := MSetList.MakeRaw (BregOrderListSetType).

(* TODO: we select another way: using ListSet, but add a sort before reloading etc...
Definition listset := BregOrderListSet.t.

Definition set_add := BregOrderListSet.add.

Definition set_mem := BregOrderListSet.mem.

Definition set_union := BregOrderListSet.union.

Definition set_ok := BregOrderListSet.Ok. *)
(*
Inductive freg: Type := F0 | F1 | F2. *)

(*
Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined. *)

Definition breg_eqb (r r': breg): bool :=
  match r, r' with
  | R0, R0
  | R1, R1
  | R2, R2
  | R3, R3
  | R4, R4
  | R5, R5
  | R6, R6
  | R7, R7
  | R8, R8
  | R9, R9
  | R10, R10 => true
  | _, _ => false
  end.

Lemma breg_eqb_true:
  forall x y, x = y <-> breg_eqb x y = true.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

Lemma breg_eqb_false:
  forall x y, x <> y <-> breg_eqb x y = false.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

Lemma breg_eqb_same:
  forall x,breg_eqb x x = true.
Proof.
  intros.
  rewrite <- breg_eqb_true.
  reflexivity.
Qed.

(** We model the following registers of the eBPF architecture. *)

Inductive bpreg :=
| BR : breg -> bpreg  (**r integer registers *) (*
| FR : freg -> bpreg  (**r float registers, not available in eBPF *)
| SP : preg          (**r hardware stack pointer register *)
| RA : preg          (**r return address register reusing the target platform *) *)
| BPC : bpreg.         (**r program counter *)


Coercion BR: breg >-> bpreg. (*
Coercion FR: freg >-> bpreg. *)

Lemma bpreg_eq: forall (x y: bpreg), {x=y} + {x<>y}.
Proof. decide equality. apply breg_eq. (* apply freg_eq. *)
Defined.

Module BPregEq.
  Definition t  := bpreg.
  Definition eq := bpreg_eq.
End BPregEq.

Module BPregmap := EMap(BPregEq).

Definition int_of_breg (i: breg): int := Int.repr (z_of_breg i).

Definition z_of_preg (r: bpreg): Z :=
  match r with
  | BR i => z_of_breg i
  | BPC => 11 (*
  | FR _ => 0 (**r unused *) *)
  end.

(** The instruction set.  Most instructions correspond exactly to
  actual instructions of the eBPF instructions set. See the eBPF
  reference manuals for more details.  Some instructions,
  described below, are pseudo-instructions: they expand to
  canned instruction sequences during the printing of the assembly
  code. *)
(*
Definition off := Ptrofs.int. (* 16 bits *) *)
Definition off := int. (* 16 bits *)
Definition imm := int. (* 32 bits *)
Definition label := positive.

Inductive aluOp : Type :=
  | ADD   (**r dst += src *)
  | SUB   (**r dst -= src *)
  | MUL   (**r dst *= src *)
  | DIV   (**r dst /= src *)
  | OR    (**r dst |= src *)
  | AND   (**r dst &= src *)
  | LSH   (**r dst <<= src *)
  | RSH   (**r dst >>= src (unsigned) *)
  | NEG   (**r dst = ~src *)
  | MOD   (**r dst %= src *)
  | XOR   (**r dst ^= src *)
  | MOV   (**r dst = src *)
  | ARSH. (**r dst >>= src (signed) *)

Definition aluOp_eqb (op op': aluOp): bool :=
  match op, op' with
  | ADD, ADD
  | SUB, SUB
  | MUL, MUL
  | DIV, DIV
  | OR,  OR
  | AND, AND
  | LSH, LSH
  | RSH, RSH
  | NEG, NEG
  | MOD, MOD
  | XOR, XOR
  | MOV, MOV
  | ARSH, ARSH => true
  | _, _ => false
  end.

Lemma aluOp_eqb_true:
  forall x y, x = y <-> aluOp_eqb x y = true.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

Lemma aluOp_eqb_false:
  forall x y, x <> y <-> aluOp_eqb x y = false.
Proof.
  destruct x, y; simpl; intuition congruence.
Qed.

Lemma aluOp_eqb_same:
  forall x, aluOp_eqb x x = true.
Proof.
  intros.
  rewrite <- aluOp_eqb_true; auto.
Qed.

Inductive cmpOp : Type :=
  | EQ: cmpOp                (**r e1 == e2 *)
  | NE: cmpOp                (**r e1 != e2 *)
  | SET: cmpOp               (**r e1 &  e2 *)
  | GT: signedness -> cmpOp  (**r e1 >  e2 *)
  | GE: signedness -> cmpOp  (**r e1 >= e2 *)
  | LT: signedness -> cmpOp  (**r e1 <  e2 *)
  | LE: signedness -> cmpOp. (**r e1 <= e2 *)

Inductive sizeOp : Type :=
  (** 32 bits *)
| Byte        (**r 1 byte *)
| HalfWord    (**r 2 bytes *)
| Word        (**r 4 bytes *) (*
| WordAny     (**r 4 bytes *) *)
  (** 64 bits *) (*
| SignedWord (**r 4 bytes (signed) *)
| DBWord     (**r 8 bytes *)
| DBWordAny.  (**r 8 bytes *) *)
.

Inductive instruction : Type :=
  | Pload : sizeOp -> breg -> breg -> off -> instruction        (**r dereference load *)
  | Pstore : sizeOp -> breg -> breg+imm -> off -> instruction   (**r dereference store *)
  | Palu32 : aluOp -> breg -> breg+imm -> instruction           (**r arithmetics *)
  | Pjmp : off -> instruction                                 (**r unconditional jump *)
  | Pjmpcmp : cmpOp -> breg -> breg+imm -> off -> instruction (**r conditional jump with comparison *)
  | Pcall : ident -> signature -> instruction                   (**r function call *)
  | Pret : instruction.                                         (**r function return *)

Declare Scope bpf_asm.
Definition code := list int64.
Definition bpf_code := list instruction.
Definition bin_code := list int.
Record function : Type := mkfunction {fn_sig: signature; fn_code: code}.
Definition fundef := AST.fundef function.

Definition MAX_BPF_LIST_INPUT: nat := 5000.

Definition regset := BPregmap.t val.
Definition genv := Genv.t fundef unit.

Notation "a # b" := (a b) (at level 1, only parsing) : bpf_asm.
Notation "a # b <- c" := (BPregmap.set b c a) (at level 1, b at next level) : bpf_asm.


Open Scope bpf_asm.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)


Inductive outcome : Type :=
  | Next: regset -> mem -> outcome
  | Stuck: outcome.


(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]). *)

Definition nextinstr (rs: regset) :=
  rs#BPC <- (Val.add rs#BPC Vone).

Definition goto_label (c: code) (ofs: off) (rs: regset) (m: mem):=
  Next (rs#BPC <- (Val.add (Val.add rs#BPC (Vint ofs)) Vone)) m.

Definition eval_reg_imm (rs : regset) (ri: breg+imm) : val :=
  match ri with
  | inl r => rs#r
  | inr i => Vint i
  end.

(** Evaluation of [Palu] operands *)

Definition eval_alu32 (b: aluOp) (v1 v2: val) : option val :=
  match b with
  | ADD => Some (Val.add v1 v2)
  | SUB => Some (Val.sub v1 v2)
  | MUL => Some (Val.mul v1 v2)
  | DIV => Val.divu v1 v2
  | OR  => Some (Val.or v1 v2)
  | AND => Some (Val.and v1 v2)
  | LSH => Some (Val.shl v1 v2)
  | RSH => Some (Val.shru v1 v2)
  | NEG => Some (Val.neg v2)
  | MOD => Val.modu v1 v2
  | XOR => Some (Val.xor v1 v2)
  | MOV => Some v2
  | ARSH => Some (Val.shr v1 v2)
  end.

(** Evaluation of [Pcmp] and [Pjmpcmp] operands *)

Definition eval_cmp (op: cmpOp) (rs: regset) (m: mem) (r: breg) (ri: breg+imm) : option bool :=
  match op with
  | EQ          => Val.cmpu_bool  (Mem.valid_pointer m) Ceq (rs#r) (eval_reg_imm rs ri)
  | GT Signed   => Val.cmp_bool Cgt (rs#r) (eval_reg_imm rs ri)
  | GT Unsigned => Val.cmpu_bool  (Mem.valid_pointer m) Cgt (rs#r) (eval_reg_imm rs ri)
  | GE Signed   => Val.cmp_bool Cge (rs#r) (eval_reg_imm rs ri)
  | GE Unsigned => Val.cmpu_bool  (Mem.valid_pointer m) Cge (rs#r) (eval_reg_imm rs ri)
  | LT Signed   => Val.cmp_bool Clt (rs#r) (eval_reg_imm rs ri)
  | LT Unsigned => Val.cmpu_bool  (Mem.valid_pointer m) Clt (rs#r) (eval_reg_imm rs ri)
  | LE Signed   => Val.cmp_bool Cle (rs#r) (eval_reg_imm rs ri)
  | LE Unsigned => Val.cmpu_bool  (Mem.valid_pointer m) Cle (rs#r) (eval_reg_imm rs ri)
  | SET         => Val.cmpu_bool  (Mem.valid_pointer m) Cne (Val.and (rs#r) (eval_reg_imm rs ri)) (Vint Int.zero)
  | NE          => Val.cmpu_bool  (Mem.valid_pointer m) Cne (rs#r) (eval_reg_imm rs ri)
  end.


(** Auxiliaries for memory accesses *)
Definition sizeOp2chunk (k: sizeOp) : memory_chunk :=
  match k with
  | Byte => Mint8unsigned
  | HalfWord => Mint16unsigned
  | Word     => Mint32
  end.

Definition exec_load (k: sizeOp) (r: breg) (addr: val) (rs: regset) (m:mem) :=
  match Mem.loadv (sizeOp2chunk k) m addr with
  | None => Stuck
  | Some v =>
    match v with (**r Vint should be checked by an invaraint or something like verifier? *)
    | Vint vi => Next (nextinstr (rs#r <- (Vint vi))) m
    | _ => Stuck
    end
  end.

Definition exec_store (k: sizeOp) (ri: breg+imm) (addr: val) (rs: regset) (m:mem) :=
  match Mem.storev (sizeOp2chunk k) m addr (eval_reg_imm rs ri) with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

Definition exec_alu32 (o: aluOp)  (r: breg) (ri: breg+imm) (rs: regset) (m: mem) :=
  match eval_alu32 o (rs#r) (eval_reg_imm rs ri) with
  | None => Stuck
  | Some v =>
    match v with (**r Vint should be checked by an invaraint or something like verifier? *)
    | Vint vi => Next (nextinstr (rs#r <- (Vint vi))) m
    | _ => Stuck
    end
  end.

Fixpoint exec_alu32_list (l: bpf_code) (rs: regset) (m: mem) :=
  match l with
  | [] => Next rs m
  | hd :: tl =>
    match hd with
    | Palu32 op dst src =>
      match exec_alu32 op dst src rs m with
      | Stuck => Stuck
      | Next rs' m' => exec_alu32_list tl rs' m'
      end
    | _ => Stuck
    end
  end.

Definition exec_cmp (r: breg) (rs: regset) (m: mem) (res: option bool) :=
  Next (nextinstr (rs#r <- (Val.of_optbool res))) m.

Definition exec_branch (c: code) (l: off) (rs: regset) (m: mem) (res: option bool) : outcome :=
  match res with
  | Some true  => goto_label c l rs m
  | Some false => Next (nextinstr rs) m
  | None => Stuck
  end.

Definition z_of_sizeOp (k: sizeOp): Z :=
  match k with
  | Byte => 1
  | HalfWord => 2
  | Word     => 4
  end.

Definition max_ofs (ofs: int) (k: sizeOp): bool :=
  negb (Int.ltu (Int.repr (Int.max_unsigned - (z_of_sizeOp k))%Z) ofs).

Inductive state: Type :=
  | State: regset -> mem -> state.
