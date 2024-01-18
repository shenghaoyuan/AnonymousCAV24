From compcert Require Import Integers.

From bpf.rbpf32 Require Import TSSyntax TSDecode.

From Coq Require Import List ZArith Arith String Lia.
Import ListNotations.
Open Scope nat_scope.

Definition is_alu32 (ins: instruction): bool :=
  match ins with
  | Palu32 op dst src => true
  | _ => false
  end.

Fixpoint get_alu32_list (c: code) (fuel pc: nat): option bpf_code :=
  match fuel with
  | O => None
  | S n =>
    match List.nth_error c pc with
    | None => None
    | Some ins =>
      match decode_ind ins with
      | None => None
      | Some bpf_ins =>
        if is_alu32 bpf_ins then
          match get_alu32_list c n (S pc) with
          | None => None
          | Some tl => Some (bpf_ins :: tl)
          end
        else
          Some []
      end
    end
  end.

Fixpoint analyzer_aux (c: code) (fuel pc: nat): option (list (nat * bpf_code)) :=
  match fuel with
  | O => Some []
  | S n =>
    if (Nat.eqb (List.length c) pc) then
      Some []
    else
    match find_instr pc c with
    | None => None
    | Some bpf_ins =>
      match bpf_ins with
      | Palu32 _ _ _ =>
        match get_alu32_list c (List.length c - pc) pc with
        | None => None
        | Some l1 =>
          match analyzer_aux c n (pc + List.length l1) with
          | None => None
          | Some l => Some ((pc, l1) :: l)
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
                match analyzer_aux c n (S pc) with
                | None => None
                | Some l => Some ((lbl, l1) :: l)
                end
              end
            | _ => analyzer_aux c n (S pc)
            end
          end
      | _ => (**r when ins is not jump *)
        analyzer_aux c n (S pc)
      end
    end
  end.

Definition analyzer (c: code): option (list (nat * bpf_code)) :=
  analyzer_aux c (List.length c) 0%nat.

(**r TODO: unused *)
Lemma get_alu32_list_prop: forall k pc c ins bi l,
    List.nth_error c pc = Some ins ->
    decode_ind ins = Some bi ->
    is_alu32 bi = true ->
    k <= List.length c ->
    get_alu32_list c k pc = Some l ->
      nth_error l 0 = Some bi.
Proof.
  destruct k; simpl; intros pc c ins bi l Hnth HD HALU HLE Hget.
  - inversion Hget.
  - rewrite Hnth in Hget.
    rewrite HD in Hget.
    rewrite HALU in Hget.
    destruct get_alu32_list eqn: Hget1; [| inversion Hget].
    injection Hget as Heq; subst l.
    f_equal.
Qed.

Definition instruction_alu32_eqb (i i': instruction): bool :=
  match i, i' with
  | Palu32 op dst src, Palu32 op' dst' src' =>
    (aluOp_eqb op op') &&
    (breg_eqb dst dst') &&
    ( match src, src' with
      | inl r, inl r' => breg_eqb r r'
      | inr ri, inr ri' => Int.eq ri ri'
      | _, _ => false
      end)
  | _, _ => false
  end.

Fixpoint code_subset (l: bpf_code) (n: nat) (c: code): bool :=
  match l with
  | [] => true
  | hd :: tl =>
    match List.nth_error c n with
    | None => false
    | Some ins =>
      match decode_ind ins with
      | None => false
      | Some bpf_ins =>
        if instruction_alu32_eqb hd bpf_ins then
          code_subset tl (S n) c
        else
          false
      end
    end
  end.

Lemma get_alu32_list_code_subset:
  forall n c l,
    get_alu32_list c n (List.length c - n) = Some l ->
    n <= List.length c ->
      code_subset l (List.length c - n) c = true.
Proof.
  induction n; simpl; intros c l Hget HLE.
  - inversion Hget.
  - destruct nth_error as [ins |] eqn: Hnth; [| inversion Hget].
    destruct decode_ind as [bpf_ins |] eqn: Hbpf; [| inversion Hget].
    destruct is_alu32 eqn: Halu32.
    + destruct get_alu32_list as [tl | ] eqn: HgetS; [| inversion Hget].
      injection Hget as Heq; subst l.
      simpl.
      replace (S (Datatypes.length c - S n)) with (Datatypes.length c - n) in * by lia.
      rewrite Hnth, Hbpf.
      unfold is_alu32 in Halu32.
      destruct bpf_ins; inversion Halu32.
      simpl.
      rewrite aluOp_eqb_same, breg_eqb_same.
      simpl.
      destruct s.
      * rewrite breg_eqb_same.
        eapply IHn; eauto. lia.
      * rewrite Int.eq_true.
        eapply IHn; eauto. lia.
    + injection Hget as Heq; subst l.
      simpl.
      auto.
Qed.

Lemma analyzer_aux_code_subset: forall k t c kl ep l,
    analyzer_aux c k t = Some kl ->
    k <= List.length c ->
    In (ep,l) kl ->
      code_subset l ep c = true.
Proof.
  induction k; intros t c kl ep l HA HK Hin.
  - simpl in HA.
    injection HA as Heq; subst kl.
    inversion Hin.
  - simpl in HA.

    destruct (_ =? _) eqn: Heq_len.
    { injection HA as Heq; subst kl.
      inversion Hin.
    }

    unfold find_instr in HA.
    destruct nth_error as [ins | ] eqn: Hnth; [| inversion HA].
    destruct decode_ind as [bpf_ins | ] eqn: Hbpf; [| inversion HA].
    destruct bpf_ins; try (eapply IHk; eauto; lia).
    + destruct get_alu32_list as [l1 | ] eqn: Hget; [| inversion HA].
      destruct analyzer_aux as [lt | ] eqn: Haux; [injection HA as Heq; subst kl | inversion HA].
      simpl in Hin.
      destruct Hin as [Heq | Hin].
      * injection Heq as Heq1 Heq2; subst t; subst l1.
        assert (Hle: ep < List.length c). {
          clear - Hnth.
          eapply nth_error_Some; eauto.
          rewrite Hnth. intro HF; inversion HF.
        }
        remember (Datatypes.length c - ep) as n eqn: Hneq.
        assert (Heq: ep = (Datatypes.length c - n)) by lia.
        subst ep.
        eapply get_alu32_list_code_subset in Hget; eauto. lia.
      * eapply IHk; eauto. lia.

    + destruct nth_error as [insk | ] eqn: Hnthk in HA; [| inversion HA].
      destruct decode_ind as [bpf_insk | ] eqn: Hbpfk in HA; [| inversion HA].
      destruct bpf_insk; try (eapply IHk; eauto; lia).
      destruct get_alu32_list as [l1 | ] eqn: Hget in HA; [| inversion HA].
      destruct analyzer_aux as [lt | ] eqn: Haux; [injection HA as Heq; subst kl | inversion HA].
      simpl in Hin.
      destruct Hin as [Heq | Hin].
      * injection Heq as Heq1 Heq2; subst l1.
        rewrite Heq1 in *; clear Heq1.
        assert (Hle: ep < List.length c). {
          clear - Hnthk.
          eapply nth_error_Some; eauto.
          rewrite Hnthk. intro HF; inversion HF.
        }
        remember (Datatypes.length c - ep) as n eqn: Hneq.
        assert (Heq: ep = (Datatypes.length c - n)) by lia.
        subst ep.
        eapply get_alu32_list_code_subset in Hget; eauto. lia.
      * eapply IHk; eauto. lia.
    + destruct nth_error as [insk | ] eqn: Hnthk in HA; [| inversion HA].
      destruct decode_ind as [bpf_insk | ] eqn: Hbpfk in HA; [| inversion HA].
      destruct bpf_insk; try (eapply IHk; eauto; lia).
      destruct get_alu32_list as [l1 | ] eqn: Hget in HA; [| inversion HA].
      destruct analyzer_aux as [lt | ] eqn: Haux; [injection HA as Heq; subst kl | inversion HA].
      simpl in Hin.
      destruct Hin as [Heq | Hin].
      * injection Heq as Heq1 Heq2; subst l1.
        rewrite Heq1 in *; clear Heq1.
        assert (Hle: ep < List.length c). {
          clear - Hnthk.
          eapply nth_error_Some; eauto.
          rewrite Hnthk. intro HF; inversion HF.
        }
        remember (Datatypes.length c - ep) as n eqn: Hneq.
        assert (Heq: ep = (Datatypes.length c - n)) by lia.
        subst ep.
        eapply get_alu32_list_code_subset in Hget; eauto. lia.
      * eapply IHk; eauto. lia.
Qed.


Lemma analyzer_code_subset: forall k c kl ep l,
    analyzer c = Some kl ->
    k <= List.length c ->
    In (ep,l) kl ->
      code_subset l ep c = true.
Proof.
  unfold analyzer; intros k c kl ep l HA Hin HLE.
  eapply analyzer_aux_code_subset in HA; eauto.
Qed.

(* TODO: 
Lemma get_alu32_list_kl_max_len:
  forall n c l,
    get_alu32_list c n (List.length c - n) = Some l ->
    n <= List.length c ->
    List.length c <= MAX_BPF_LIST_INPUT ->
      List.length l <= MAX_BPF_LIST_INPUT.
Proof.
  unfold MAX_BPF_LIST_INPUT.
  induction n; intros c l Hget HL HE.
  - simpl in *. inversion Hget.
  - simpl in Hget.
    destruct nth_error
Qed.

Lemma analyzer_aux_kl_max_len: forall k t c kl ep l,
    analyzer_aux c k t = Some kl ->
    k <= List.length c ->
    List.length c <= MAX_BPF_LIST_INPUT ->
    In (ep,l) kl ->
      List.length l <= MAX_BPF_LIST_INPUT.
Proof.
  unfold MAX_BPF_LIST_INPUT.
  induction k; intros t c kl ep l HA HK HE Hin.
  - simpl in HA.
    injection HA as Heq; subst kl.
    inversion Hin.
  - simpl in HA.
    unfold find_instr in HA.
    unfold find_instr in HA.
    destruct nth_error as [ins | ] eqn: Hnth; [| inversion HA].
    destruct decode_ind as [bpf_ins | ] eqn: Hbpf; [| inversion HA].
    destruct bpf_ins; try (eapply IHk; eauto; lia).
    + destruct get_alu32_list as [l1 | ] eqn: Hget; [| inversion HA].
      destruct analyzer_aux as [lt | ] eqn: Haux; [injection HA as Heq; subst kl | inversion HA].
      simpl in Hin.
      destruct Hin as [Heq | Hin].
      * injection Heq as Heq1 Heq2; subst t; subst l1.
        assert (Hle: ep < List.length c). {
          clear - Hnth.
          eapply nth_error_Some; eauto.
          rewrite Hnth. intro HF; inversion HF.
        }
        remember (Datatypes.length c - ep) as n eqn: Hneq.
        assert (Heq: ep = (Datatypes.length c - n)) by lia.
        subst ep.
        eapply get_alu32_list_code_subset in Hget; eauto. lia.
      * eapply IHk; eauto. lia.

    + destruct nth_error as [insk | ] eqn: Hnthk in HA; [| inversion HA].
      destruct decode_ind as [bpf_insk | ] eqn: Hbpfk in HA; [| inversion HA].
      destruct bpf_insk; try (eapply IHk; eauto; lia).
      destruct get_alu32_list as [l1 | ] eqn: Hget in HA; [| inversion HA].
      destruct analyzer_aux as [lt | ] eqn: Haux; [injection HA as Heq; subst kl | inversion HA].
      simpl in Hin.
      destruct Hin as [Heq | Hin].
      * injection Heq as Heq1 Heq2; subst l1.
        rewrite Heq1 in *; clear Heq1.
        assert (Hle: ep < List.length c). {
          clear - Hnthk.
          eapply nth_error_Some; eauto.
          rewrite Hnthk. intro HF; inversion HF.
        }
        remember (Datatypes.length c - ep) as n eqn: Hneq.
        assert (Heq: ep = (Datatypes.length c - n)) by lia.
        subst ep.
        eapply get_alu32_list_code_subset in Hget; eauto. lia.
      * eapply IHk; eauto. lia.
    + destruct nth_error as [insk | ] eqn: Hnthk in HA; [| inversion HA].
      destruct decode_ind as [bpf_insk | ] eqn: Hbpfk in HA; [| inversion HA].
      destruct bpf_insk; try (eapply IHk; eauto; lia).
      destruct get_alu32_list as [l1 | ] eqn: Hget in HA; [| inversion HA].
      destruct analyzer_aux as [lt | ] eqn: Haux; [injection HA as Heq; subst kl | inversion HA].
      simpl in Hin.
      destruct Hin as [Heq | Hin].
      * injection Heq as Heq1 Heq2; subst l1.
        rewrite Heq1 in *; clear Heq1.
        assert (Hle: ep < List.length c). {
          clear - Hnthk.
          eapply nth_error_Some; eauto.
          rewrite Hnthk. intro HF; inversion HF.
        }
        remember (Datatypes.length c - ep) as n eqn: Hneq.
        assert (Heq: ep = (Datatypes.length c - n)) by lia.
        subst ep.
        eapply get_alu32_list_code_subset in Hget; eauto. lia.
      * eapply IHk; eauto. lia.
  
Qed.


Lemma analyzer_kl_max_len: forall k c kl ep l,
    analyzer c = Some kl ->
    k <= List.length c ->
    In (ep,l) kl ->
      code_subset l ep c = true.
    List.length c <= MAX_BPF_LIST_INPUT -> *)