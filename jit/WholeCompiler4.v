From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.arm Require Import ABinSem BinDecode.

From bpf.comm Require Import ListAsArray JITCall.
From bpf.rbpf32 Require Import JITConfig TSSyntax TSDecode Analyzer.
From bpf.jit Require Import ThumbJIT WholeCompiler WholeCompilerGeneric WholeCompiler1.
From bpf.jit Require Import WholeCompiler2 ThumbJIT1 ListSetRefinement ThumbJIT1proof ListSetSort.
From bpf.jit Require Import ThumbJIT2 WholeCompiler3.

From Coq Require Import List ZArith Arith String Lia.
Import ListNotations.
Open Scope nat_scope.
Open Scope bool_scope.
Open Scope asm.

(**r use refined listset *)

Fixpoint get_alu32_jit_list4 (c: code) (fuel pc counter: nat) (ld_set st_set: listset_regmap)
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code * listset_regmap * listset_regmap * nat):=
  match fuel with
  | O => None
  | S n =>
      match List.nth_error c pc with
      | None => None
      | Some ins =>
        match decode_ind ins with
        | None => None
        | Some bpf_ins =>
          match bpf_ins with
          | Palu32 op dst src =>
            match jit_one2 op dst src ld_set st_set tp_len tp_bin with
            | None => None
            | Some (tp_len1, tp_bin1, ld1, st1) =>
              get_alu32_jit_list4 c n (S pc) (S counter) ld1 st1 tp_len1 tp_bin1
            end
          | _ => Some (tp_len, tp_bin, ld_set, st_set, counter)
          end
        end
      end
  end.

Definition compose_jit_list_aux4 (c: code) (fuel pc counter: nat) (ld_set st_set: listset_regmap)
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code * nat):=
  match jit_alu32_pre2 tp_len tp_bin with
  | None => None
  | Some (tp_len1, tp_bin1) =>
    match get_alu32_jit_list4 c fuel pc counter ld_set st_set tp_len1 tp_bin1 with
    | None => None
    | Some (tp_len2, tp_bin2, ld_set2, st_set2, n) =>
      match jit_alu32_thumb_pc2 n tp_len2 tp_bin2 with
      | None => None
      | Some (tp_len3, tp_bin3) =>
        match jit_alu32_thumb_store2 st_set2 tp_len3 tp_bin3 with
        | None => None
        | Some (tp_len4, tp_bin4) =>
          match jit_alu32_thumb_reset2 ld_set tp_len4 tp_bin4 with
          | None => None
          | Some (tp_len5, tp_bin5) =>
            match jit_alu32_post2 tp_len5 tp_bin5 with
            | None => None
            | Some (tp_len6, tp_bin6) => Some (tp_len6, tp_bin6, n)
            end
          end
        end
      end
    end
  end.

Definition compose_jit_list4 (c: code) (fuel pc: nat)
  (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code * nat):=
  compose_jit_list_aux4 c fuel pc 0%nat init_listset_regmap init_listset_regmap tp_len tp_bin.

Fixpoint whole_compiler4_aux (c: code) (fuel pc: nat) (tp_kv: list (nat * nat))
  (tp_len: nat) (tp_bin: bin_code): option (list (nat * nat) * nat * bin_code):=
  match fuel with
  | O => Some (tp_kv, tp_len, tp_bin)
  | S n =>
    if (Nat.eqb (List.length c) pc) then
      Some (tp_kv, tp_len, tp_bin)
    else
    match find_instr pc c with
    | None => None
    | Some bpf_ins =>
      match bpf_ins with
      | Palu32 _ _ _ =>
        let base := tp_len in
        match compose_jit_list4 c (List.length c - pc) pc tp_len tp_bin with
        | None => None
        | Some (tp_len1, tp_bin1, len) =>
          whole_compiler4_aux c n (pc + len) ((pc, base) :: tp_kv) tp_len1 tp_bin1
        end

      | Pjmp ofs | Pjmpcmp _ _ _ ofs => (**r check if ins is jump *)
        let lbl := Z.to_nat (Int.signed
          (Int.add Int.one (Int.add (Int.repr (Z.of_nat pc)) ofs))) in
          match find_instr lbl c with
          | None => None
          | Some ins =>
            match ins with
            | Palu32 _ _ _ =>
              let base := tp_len in
              match compose_jit_list4 c (List.length c - lbl) lbl tp_len tp_bin with
              | None => None
              | Some (tp_len1, tp_bin1, len) =>
                whole_compiler4_aux c n (S pc) ((lbl, base) :: tp_kv) tp_len1 tp_bin1
              end
            | _ => whole_compiler4_aux c n (S pc) tp_kv tp_len tp_bin
            end
          end
      | _ => (**r when ins is not jump *)
        whole_compiler4_aux c n (S pc) tp_kv tp_len tp_bin
      end
    end
  end.

Definition whole_compiler4 (c: code):
    option (list (nat * nat) * nat * bin_code):=
  whole_compiler4_aux c (List.length c) 0%nat [] 0%nat (List32.create_int_list JITTED_LIST_MAX_LENGTH).

Fixpoint list_in_bin_code (l: bin_code) (tp_len: nat) (tp_bin: bin_code): option (nat * bin_code) :=
  match l with
  | [] => Some (tp_len, tp_bin)
  | hd :: tl =>
    match tp_bin_add tp_bin tp_len hd with
    | None => None
    | Some tp_bin1 => list_in_bin_code tl (Nat.add tp_len 1) tp_bin1
    end
  end.

Lemma list_in_bin_code_concat:
  forall l1 l2 tp_len tp_bin tp_len2 tp_bin2
  (Hsubset : list_in_bin_code (l1 ++ l2) tp_len tp_bin = Some (tp_len2, tp_bin2)),
    exists tp_len1 tp_bin1,
      list_in_bin_code l1 tp_len tp_bin = Some (tp_len1, tp_bin1) /\
      list_in_bin_code l2 tp_len1 tp_bin1 = Some (tp_len2, tp_bin2).
Proof.
  induction l1; simpl; intros.
  { eexists;eexists; split;[reflexivity | ].
    auto. }

  destruct tp_bin_add as [tp_bin1 |] eqn: Hadd; [| inversion Hsubset].
  eapply IHl1 in Hsubset; eauto.
Qed.

(*
Lemma jit_one4_eq:
  forall l1 tp_len tp_bin tp_len2 tp_bin2 a b s ld_set1 st_set1 ld1 st1
    (Hsubset1 : list_in_bin_code l1 tp_len tp_bin = Some (tp_len2, tp_bin2))
    (Hone : jit_one_refine a b s ld_set1 st_set1 = Some (l1, ld1, st1)),
    jit_one2 a b s ld_set1 st_set1 tp_len tp_bin = Some (tp_len2, tp_bin2, ld1, st1).
Proof.
  intros.
  unfold jit_one_refine in Hone.
  unfold jit_one2.
  destruct s.
  - 

../..
Qed.


Lemma get_alu32_jit_list4_eq:
  forall fuel bl pc c counter ld_set1 st_set1 ld_set2 st_set2 n tp_len tp_bin tp_len1 tp_bin1
  (Hsubset: list_in_bin_code bl tp_len tp_bin = Some (tp_len1, tp_bin1))
  (Hjit: get_alu32_jit_list_refine c fuel pc counter ld_set1 st_set1 = Some (bl, ld_set2, st_set2, n)),
      get_alu32_jit_list4 c fuel pc counter ld_set1 st_set1 tp_len tp_bin = Some (tp_len1, tp_bin1, ld_set2, st_set2, n).
Proof.
  induction fuel; simpl; intros.
  { inversion Hjit. }

  destruct nth_error as [ins32 |] eqn: Hnth; [| inversion Hjit].
  destruct decode_ind as [ins |] eqn: Hdecode; [| inversion Hjit].
  destruct ins; try (
    inversion Hjit; subst;
    simpl in Hsubset;
    inversion Hsubset; subst;
    reflexivity).

  destruct jit_one_refine as [((l1 & ld1) & st1)|] eqn: Hone; [| inversion Hjit].
  destruct get_alu32_jit_list_refine as [(((l2 & ld2) & st2) & n2)|] eqn: Halu32; [| inversion Hjit].
  inversion Hjit; subst.
  eapply list_in_bin_code_concat in Hsubset.
  destruct Hsubset as (tp_len2 & tp_bin2 & Hsubset1 & Hsubset2).
  eapply IHfuel in Halu32; eauto.
  
  ../..
Qed. *)

