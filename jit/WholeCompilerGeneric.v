From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.arm Require Import ABinSem BinDecode.

From bpf.comm Require Import JITCall.
From bpf.rbpf32 Require Import JITConfig TSSyntax TSDecode Analyzer.
From bpf.jit Require Import ListSetSort ThumbJIT WholeCompiler.

From Coq Require Import List ZArith Arith Lia.
Import ListNotations.
Open Scope nat_scope.
Open Scope bool_scope.
Open Scope asm.

(**r unfold definition, make it more generic *)
Definition whole_compiler_unfold_aux (c: code) (fuel pc base: nat):
    option (list (nat * nat) * bin_code) :=
  match analyzer_aux c fuel pc with
  | None => None
  | Some kl =>
    match kl with
    | [] => Some ([], [])
    | _ =>
      match combiner_aux kl base with
      | None => None
      | Some bl => Some (concat_bin bl)
      end
    end
  end.

Definition whole_compiler_unfold (c: code): option (list (nat * nat) * bin_code) :=
  whole_compiler_unfold_aux c (List.length c) 0%nat 0%nat.

Theorem whole_compiler_unfold_same:
  forall c,
    whole_compiler_unfold c = whole_compiler c.
Proof.
  unfold whole_compiler_unfold, whole_compiler; intros.
  unfold whole_compiler_unfold_aux, analyzer, combiner.
  reflexivity.
Qed.

Definition jit_alu32_generic_aux (l: bpf_code) (ld_set st_set: listset): option bin_code :=
  match jit_sequence l ld_set st_set with
  | None => None
  | Some (cl, ld_set, st_set) =>
    match cl with
    | [] => None (**r we don't want this case, wher should we put this check? *)
    | _ =>
      match jit_alu32_thumb_pc (List.length l) with
      | None => None
      | Some l_pc =>
        Some (jit_alu32_pre ++ cl ++ l_pc ++ (jit_alu32_thumb_store (sort_listset st_set)) ++
              (jit_alu32_thumb_reset (sort_listset ld_set)) ++ jit_alu32_post)
      end
    end
  end.

Definition jit_alu32_generic (l: bpf_code): option bin_code :=
  jit_alu32_generic_aux l [] [].

(**r getting a generic jit_alu32 and merging combiner + concat_bin = combiner_generic_aux *)
Fixpoint combiner_generic_aux (kl: list (nat * bpf_code)) (base: nat):
  option (list (nat * nat) * bin_code) :=
  match kl with
  | [] => Some ([], [])
  | (ep, l) :: tl =>
    match jit_alu32_generic l with
    | None => None
    | Some bl =>
      if Nat.ltb (base + List.length bl) JITTED_LIST_MAX_LENGTH then
        match combiner_generic_aux tl (base + (List.length bl)) with
        | None => None
        | Some (kv, cl) => Some ((ep, base) :: kv, bl ++ cl)
        end
      else
        None
    end
  end.

Definition whole_compiler_generic_aux (c: code) (fuel pc base: nat):
  option (list (nat * nat) * bin_code) :=
  match analyzer_aux c fuel pc with
  | None => None
  | Some kl =>
    match kl with
    | [] => Some ([], [])
    | _ => combiner_generic_aux kl base
    end
  end.

Definition whole_compiler_generic (c: code) : 
  option (list (nat * nat) * bin_code) :=
  whole_compiler_generic_aux c (List.length c) 0%nat 0%nat.

Lemma jit_alu32_generic_same:
  forall l,
    jit_alu32_generic l = jit_alu32 l.
Proof.
  intros.
  unfold jit_alu32_generic, jit_alu32_generic_aux, jit_alu32.
  unfold jit_alu32_aux.
  destruct jit_sequence as [((cl, ld_set), st_set) | ]; [| reflexivity].
  destruct cl as [| chd ctl]; [reflexivity|].
  destruct jit_alu32_thumb_pc as [l_pc |]; [| reflexivity].
  f_equal.
  apply app_inv_head_iff.
  repeat (rewrite <- app_assoc; apply app_inv_head_iff).
  reflexivity.
Qed.

Lemma whole_compiler_generic_aux_same:
  forall fuel c pc base kv l,
    whole_compiler_unfold_aux c fuel pc base = Some (kv, l) ->
    whole_compiler_generic_aux c fuel pc base = Some (kv, l).
Proof.
  unfold whole_compiler_unfold_aux, whole_compiler_generic_aux.
  induction fuel; simpl; intros c pc base kv l Hunfold.
  { auto. }

  destruct (_ =? _) eqn: Heq_len.
  { auto. }

  destruct find_instr as [ ins |] eqn: Hfind; [| inversion Hunfold].
  destruct ins; try (eapply IHfuel; eauto).
  - destruct get_alu32_list as [l1|] eqn: HL1; [| inversion Hunfold].
    destruct analyzer_aux as [ kl | ] eqn: Haux; [| inversion Hunfold]. (*
    destruct List.existsb eqn:He.
    {
      rewrite existsb_exists in He.
      simpl in He.
      destruct kl as [| khd ktl ] eqn: HKL; [auto |].
      simpl in Hunfold.
      simpl.
      destruct khd as (ep & ep_l).
      rewrite jit_alu32_generic_same.
      destruct jit_alu32 as [bl|] eqn: HBL; [| inversion Hunfold].
      destruct combiner_aux eqn: Hcombiner; [| inversion Hunfold].
      injection Hunfold as Heq1 Heq2.
      specialize (IHfuel c (pc + Datatypes.length l1) base kv l).
      subst kv.
      subst l.
      rewrite Haux in IHfuel.
      simpl in IHfuel.
      rewrite HBL in IHfuel.
      rewrite Hcombiner in IHfuel.
      assert (Heq: Some (concat_bin ((ep, (base, bl)) :: l0)) =
         Some ((ep, base) :: fst (concat_bin l0), bl ++ snd (concat_bin l0))). {
        f_equal.
      }
      specialize (IHfuel Heq).
      rewrite jit_alu32_generic_same in IHfuel.
      rewrite HBL in IHfuel.
      auto.
    } *)

    destruct kl as [| khd ktl ] eqn: HKL; [|].
    { simpl in Hunfold.
      simpl.
      rewrite jit_alu32_generic_same.
      destruct jit_alu32 as [bl|] eqn: HBL; [| inversion Hunfold].
      destruct (_ <? _) eqn: Hcond; [| inversion Hunfold].
      simpl in Hunfold. auto.
    }

    rewrite <- HKL in *.
    simpl in Hunfold.
    simpl.
    rewrite jit_alu32_generic_same.
    destruct jit_alu32 as [bl|] eqn: HBL; [| inversion Hunfold].
    destruct (_ <? _) eqn: Hcond; [| inversion Hunfold].

    destruct combiner_aux as [cl |] eqn: HCL;[| inversion Hunfold].
    injection Hunfold as HKV_eq HL_eq.

    specialize (IHfuel c ((pc + Datatypes.length l1)) (base + Datatypes.length bl)
        (fst (concat_bin cl))
        (snd (concat_bin cl))).
    rewrite Haux in IHfuel.
    rewrite HKL in *.
    rewrite HCL in IHfuel.
    assert (Heq: Some (concat_bin cl) = Some (fst (concat_bin cl), snd (concat_bin cl)))
      by (f_equal; apply surjective_pairing; auto).
    specialize (IHfuel Heq); clear Heq.
    rewrite IHfuel.
    rewrite HKV_eq, HL_eq; f_equal.
  - destruct find_instr as [ins_pc|] eqn: Hfind_pc in Hunfold; [| inversion Hunfold].
    rewrite Hfind_pc.
    destruct ins_pc; try (eapply IHfuel; eauto).
    destruct get_alu32_list as [l1|] eqn: HL1; [| inversion Hunfold].
    destruct analyzer_aux as [ kl | ] eqn: Haux; [| inversion Hunfold]. (*

    destruct List.existsb eqn:He.
    {
      rewrite existsb_exists in He.
      simpl in He.
      destruct kl as [| khd ktl ] eqn: HKL; [auto |].
      simpl in Hunfold.
      simpl.
      destruct khd as (ep & ep_l).
      rewrite jit_alu32_generic_same.
      destruct jit_alu32 as [bl|] eqn: HBL; [| inversion Hunfold].
      destruct combiner_aux eqn: Hcombiner; [| inversion Hunfold].
      injection Hunfold as Heq1 Heq2.
      specialize (IHfuel c (S pc) base kv l).
      subst kv.
      subst l.
      rewrite Haux in IHfuel.
      simpl in IHfuel.
      rewrite HBL in IHfuel.
      rewrite Hcombiner in IHfuel.
      assert (Heq: Some (concat_bin ((ep, (base, bl)) :: l0)) =
         Some ((ep, base) :: fst (concat_bin l0), bl ++ snd (concat_bin l0))). {
        f_equal.
      }
      specialize (IHfuel Heq).
      rewrite jit_alu32_generic_same in IHfuel.
      rewrite HBL in IHfuel.
      auto.
    } *)


    destruct kl as [| khd ktl ] eqn: HKL; [|].
    { simpl in Hunfold.
      simpl.
      rewrite jit_alu32_generic_same.
      destruct jit_alu32 as [bl|] eqn: HBL; [| inversion Hunfold].
      destruct (_ <? _) eqn: Hcond; [| inversion Hunfold].
      simpl in Hunfold. auto.
    }

      rewrite <- HKL in *.
      simpl in Hunfold.
      simpl.

      rewrite jit_alu32_generic_same.
      destruct jit_alu32 as [bl|] eqn: HBL; [| inversion Hunfold].
      destruct (_ <? _) eqn: Hcond; [| inversion Hunfold].

      destruct combiner_aux as [cl |] eqn: HCL;[| inversion Hunfold].
      injection Hunfold as HKV_eq HL_eq.

      specialize (IHfuel c (S pc) (base + Datatypes.length bl)
        (fst (concat_bin cl))
        (snd (concat_bin cl))).
      rewrite Haux in IHfuel.
      rewrite HKL in *.
      rewrite HCL in IHfuel.
      assert (Heq: Some (concat_bin cl) = Some (fst (concat_bin cl), snd (concat_bin cl)))
        by (f_equal; apply surjective_pairing; auto).
      specialize (IHfuel Heq); clear Heq.
      rewrite IHfuel.
      rewrite HKV_eq, HL_eq; f_equal.

  - destruct find_instr as [ins_pc|] eqn: Hfind_pc in Hunfold; [| inversion Hunfold].
    rewrite Hfind_pc.
    destruct ins_pc; try (eapply IHfuel; eauto).
      destruct get_alu32_list as [l1|] eqn: HL1; [| inversion Hunfold].
      destruct analyzer_aux as [ kl | ] eqn: Haux; [| inversion Hunfold]. (*

    destruct List.existsb eqn:He.
    {
      rewrite existsb_exists in He.
      simpl in He.
      destruct kl as [| khd ktl ] eqn: HKL; [auto |].
      simpl in Hunfold.
      simpl.
      destruct khd as (ep & ep_l).
      rewrite jit_alu32_generic_same.
      destruct jit_alu32 as [bl|] eqn: HBL; [| inversion Hunfold].
      destruct combiner_aux eqn: Hcombiner; [| inversion Hunfold].
      injection Hunfold as Heq1 Heq2.
      specialize (IHfuel c (S pc) base kv l).
      subst kv.
      subst l.
      rewrite Haux in IHfuel.
      simpl in IHfuel.
      rewrite HBL in IHfuel.
      rewrite Hcombiner in IHfuel.
      assert (Heq: Some (concat_bin ((ep, (base, bl)) :: l0)) =
         Some ((ep, base) :: fst (concat_bin l0), bl ++ snd (concat_bin l0))). {
        f_equal.
      }
      specialize (IHfuel Heq).
      rewrite jit_alu32_generic_same in IHfuel.
      rewrite HBL in IHfuel.
      auto.
    } *)

      destruct kl as [| khd ktl ] eqn: HKL; [|].
      { simpl in Hunfold.
        simpl.
        rewrite jit_alu32_generic_same.
        destruct jit_alu32 as [bl|] eqn: HBL; [| inversion Hunfold].
        destruct (_ <? _) eqn: Hcond; [| inversion Hunfold].
        simpl in Hunfold. auto.
      }

      rewrite <- HKL in *.
      simpl in Hunfold.
      simpl.
      rewrite jit_alu32_generic_same.
      destruct jit_alu32 as [bl|] eqn: HBL; [| inversion Hunfold].
      destruct (_ <? _) eqn: Hcond; [| inversion Hunfold].

      destruct combiner_aux as [cl |] eqn: HCL;[| inversion Hunfold].
      injection Hunfold as HKV_eq HL_eq.

      specialize (IHfuel c (S pc) (base + Datatypes.length bl)
        (fst (concat_bin cl))
        (snd (concat_bin cl))).
      rewrite Haux in IHfuel.
      rewrite HKL in *.
      rewrite HCL in IHfuel.
      assert (Heq: Some (concat_bin cl) = Some (fst (concat_bin cl), snd (concat_bin cl)))
        by (f_equal; apply surjective_pairing; auto).
      specialize (IHfuel Heq); clear Heq.
      rewrite IHfuel.
      rewrite HKV_eq, HL_eq; f_equal.
Qed.

Theorem whole_compiler_generic_same:
  forall c kv l,
    whole_compiler_unfold c = Some (kv, l) ->
    whole_compiler_generic c = Some (kv, l).
Proof.
  unfold whole_compiler_unfold, whole_compiler_generic; intros.
  eapply whole_compiler_generic_aux_same; eauto.
Qed.