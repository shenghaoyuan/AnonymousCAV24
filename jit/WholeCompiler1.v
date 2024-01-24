From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.arm Require Import ABinSem BinDecode.

From bpf.comm Require Import JITCall.
From bpf.rbpf32 Require Import JITConfig TSSyntax TSDecode Analyzer.
From bpf.jit Require Import ThumbJIT WholeCompiler WholeCompilerGeneric.

From Coq Require Import List ZArith Arith String Lia.
Import ListNotations.
Open Scope nat_scope.
Open Scope bool_scope.
Open Scope asm.

(**r merging analyzer + generic combiner = whole_compiler1_aux, ie generic JIT compiler *)
Fixpoint whole_compiler1_aux (c: code) (fuel pc base: nat):
    option (list (nat * nat) * bin_code) :=
  match fuel with
  | O => Some ([], [])
  | S n =>
    if (Nat.eqb (List.length c) pc) then
      Some ([], [])
    else
    match find_instr pc c with
    | None => None
    | Some bpf_ins =>
      match bpf_ins with
      | Palu32 _ _ _ =>
        match get_alu32_list c (List.length c - pc) pc with
        | None => None
        | Some l1 =>
          match jit_alu32_generic l1 with
          | None => None
          | Some bl =>
            if Nat.ltb (base + List.length bl) JITTED_LIST_MAX_LENGTH then
              match whole_compiler1_aux c n (pc + List.length l1) (base + (List.length bl)) with
              | None => None
              | Some (kv, l) => Some ((pc, base) :: kv, bl ++ l) (*
                if (List.existsb (fun x => Nat.eqb (fst x) pc) kv) then
                  Some (kv, l)
                else
                  Some ((pc, base) :: kv, bl ++ l) *)
              end
            else
              None
          end
        end

      | Pjmp ofs | Pjmpcmp _ _ _ ofs => (**r check if ins is jump *)
        let lbl := Z.to_nat (Int.signed
          (Int.add Int.one (Int.add (Int.repr (Z.of_nat pc)) ofs))) in
          match find_instr lbl c with
          | None => None
          | Some ins =>
            match ins with
            | Palu32 _ _ _ =>
              match get_alu32_list c (List.length c - lbl) lbl with
              | None => None
              | Some l1 =>
                match jit_alu32_generic l1 with
                | None => None
                | Some bl =>
                  if Nat.ltb (base + List.length bl) JITTED_LIST_MAX_LENGTH then
                    match whole_compiler1_aux c n (S pc) (base + (List.length bl)) with
                    | None => None
                    | Some (kv, l) => Some ((lbl, base) :: kv, bl ++ l) (*
                      if (List.existsb (fun x => Nat.eqb (fst x) lbl) kv) then
                        Some (kv, l)
                      else
                        Some ((lbl, base) :: kv, bl ++ l) *)
                    end
                  else
                    None
                end
              end
            | _ => whole_compiler1_aux c n (S pc) base
            end
          end
      | _ => (**r when ins is not jump *)
        whole_compiler1_aux c n (S pc) base
      end
    end
  end.

Definition whole_compiler1 (c: code):
    option (list (nat * nat) * bin_code) :=
  whole_compiler1_aux c (List.length c) 0%nat 0%nat.

(*
Search jit_alu32.
Lemma jit_alu32_exists:
  forall fuel c pc l1
    (HL1 : get_alu32_list c fuel pc = Some l1),
      exists bl, jit_alu32 l1 = Some bl.
Proof.
  induction fuel; simpl; intros.
  { inversion HL1. }

  destruct (_ =? _) eqn: Hlen.
  { inversion Haux; subst.
    simpl in HE.
    inversion HE.
  }

  destruct find_instr as [ins | ] eqn: Hfind; [| inversion Haux].
  destruct ins.
  - eapply IHfuel; eauto.
  - eapply IHfuel; eauto.
  - destruct get_alu32_list as [l2 |] eqn: Hget in Haux; [| inversion Haux].
    destruct analyzer_aux as [l3 | ] eqn: Hana in Haux; [| inversion Haux].
    destruct List.existsb in Haux.
    + inversion Haux; subst.
      eapply IHfuel; eauto.
    + inversion Haux; subst.
      rewrite existsb_exists in HE.
      destruct HE as [HE |HE].
  eapply IHfuel; eauto.
Qed. *)

Lemma whole_compiler1_aux_same:
  forall fuel c pc base kv l,
    whole_compiler_generic_aux c fuel pc base = Some (kv, l) ->
    whole_compiler1_aux c fuel pc base = Some (kv, l).
Proof.
  unfold whole_compiler_generic_aux;
  induction fuel; simpl; intros c pc base kv l Haux.
  { auto. }

  destruct (_ =? _) eqn: Heq_len.
  { auto. }

  destruct find_instr as [ins|] eqn: Hfind; [| inversion Haux].
  destruct ins; try (eapply IHfuel; eauto).
  - destruct get_alu32_list as [l1|] eqn: HL1; [| inversion Haux].

    destruct analyzer_aux as [ kl | ] eqn: Haux1; [| inversion Haux]. (*

    destruct List.existsb eqn:He.
    {
      rewrite existsb_exists in He.
      simpl in He.
      destruct He as (n & HIn & Hfst).
      destruct kl as [| khd ktl ] eqn: HKL.
      { inversion HIn. }

      simpl in Haux.
      destruct khd as (ep & ep_l).
      destruct jit_alu32_generic as [bl|] eqn: Halu32 in Haux; [| inversion Haux].
      destruct combiner_generic_aux as [(kv1 & cl1) |] eqn: Hcom in Haux; [| inversion Haux].
      injection Haux as Heq1 Heq2.
      specialize (IHfuel c (pc + Datatypes.length l1) base kv l).
      rewrite Haux1 in IHfuel.
      assert (Heq: combiner_generic_aux ((ep, ep_l) :: ktl) base = Some (kv, l)). {
        simpl.
        rewrite Halu32.
        rewrite Hcom.
        f_equal.
        subst; auto.
      }
      specialize (IHfuel Heq); clear Heq.
      ../..
    } *)

    simpl in Haux.
    destruct jit_alu32_generic as [bl|] eqn: HBL; [| inversion Haux].
    destruct (_ <? _) eqn: HMAX; [| inversion Haux].

    destruct combiner_generic_aux as [ (kv1, cl1) |] eqn: HCL;[| inversion Haux].

    specialize (IHfuel c ((pc + Datatypes.length l1)) (base + Datatypes.length bl) kv1 cl1).
    rewrite Haux1 in IHfuel.

    destruct kl as [| khd ktl ] eqn: HKL; [|].
    { simpl in HCL.
      injection HCL as Heq1 Heq2; subst kv1 cl1.
      rewrite IHfuel; auto.
    }

    rewrite HCL in IHfuel.
    rewrite IHfuel; auto.
  - destruct find_instr as [ins_pc|] eqn: Hfind_pc in Haux; [| inversion Haux].
    rewrite Hfind_pc.
    destruct ins_pc; try (eapply IHfuel; eauto).

      destruct get_alu32_list as [l1|] eqn: HL1; [| inversion Haux].
      destruct analyzer_aux as [ kl | ] eqn: Haux1; [| inversion Haux].

      simpl in Haux.
      destruct jit_alu32_generic as [bl|] eqn: HBL; [| inversion Haux].
      destruct (_ <? _) eqn: HMAX; [| inversion Haux].
      destruct combiner_generic_aux as [ (kv1, cl1) |] eqn: HCL;[| inversion Haux].
      injection Haux as Hkv_eq Hl_eq; subst kv l.

      specialize (IHfuel c (S pc) (base + Datatypes.length bl) kv1 cl1).
      rewrite Haux1 in IHfuel.

      destruct kl as [| khd ktl ] eqn: HKL; [|].
      { simpl in HCL.
        injection HCL as Heq1 Heq2; subst kv1 cl1.
        rewrite IHfuel; auto.
      }

      rewrite HCL in IHfuel.
      rewrite IHfuel; auto.
  - destruct find_instr as [ins_pc|] eqn: Hfind_pc in Haux; [| inversion Haux].
    rewrite Hfind_pc.
    destruct ins_pc; try (eapply IHfuel; eauto).

      destruct get_alu32_list as [l1|] eqn: HL1; [| inversion Haux].
      destruct analyzer_aux as [ kl | ] eqn: Haux1; [| inversion Haux].

      simpl in Haux.
      destruct jit_alu32_generic as [bl|] eqn: HBL; [| inversion Haux].
      destruct (_ <? _) eqn: HMAX; [| inversion Haux].
      destruct combiner_generic_aux as [ (kv1, cl1) |] eqn: HCL;[| inversion Haux].
      specialize (IHfuel c (S pc) (base + Datatypes.length bl) kv1 cl1).
      rewrite Haux1 in IHfuel.

      destruct kl as [| khd ktl ] eqn: HKL; [|].
      { simpl in HCL.
        injection HCL as Heq1 Heq2; subst kv1 cl1.
        rewrite IHfuel; auto.
      }

      rewrite HCL in IHfuel.
      rewrite IHfuel; auto.
Qed.

Theorem whole_compiler1_same:
  forall c kv l,
    whole_compiler_generic c = Some (kv, l) ->
    whole_compiler1 c = Some (kv, l).
Proof.
  unfold whole_compiler_generic, whole_compiler1; intros.
  eapply whole_compiler1_aux_same; eauto.
Qed.