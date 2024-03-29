From Coq Require Import List Lia ZArith.
From compcert Require Import Integers Values Clight Memory.
Import ListNotations.

From bpf.clightlogic Require Import Clightlogic CorrectRel CommonLemma.

From bpf.jit.jitclight Require Import havm_interpreter.
From bpf.jit.havm Require Import HAVMState HAVMMonadOp DxHAVMInterpreter.

From bpf.jit.simulation Require Import MatchStateComm HAVMMatchState InterpreterRel.



(**

Print get_sub.
get_sub = 
fun x y : valu32_t => returnM (Val.sub x y)
     : valu32_t -> valu32_t -> M valu32_t

*)

Section Get_sub.
  Context {S: special_blocks}.

  (** The program contains our function of interest [fn] *)
  Definition p : Clight.program := prog.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  (* Definition Args : list CompilableType := [stateCompilableType].*)
  Definition args : list Type := [(val:Type); (val:Type)].
  Definition res : Type := (val:Type).

  (* [f] is a Coq Monadic function with the right type *)
  Definition f : arrow_type args (M res) := get_sub.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Definition fn: Clight.function := f_get_sub.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Definition match_arg_list : DList.t (fun x => x -> Inv _) args :=
    (dcons (stateless val32_correct)
       (dcons (stateless val32_correct)
                    (DList.DNil _))).

  (* [match_res] relates the Coq result and the C result *)
  Definition match_res : res -> Inv hybrid_state := stateless val32_correct.

  Instance correct_function_get_sub : forall a, correct_function _ p args res f fn ModNothing true match_state match_arg_list match_res a.
  Proof.
    correct_function_from_body args.
    correct_body.
    (** how to use correct_* *)
    unfold INV.
    unfold f.
    repeat intro.
    get_invariant _x.
    get_invariant _y.

    unfold stateless, val32_correct in c1, c2.
    destruct c1 as (Hc_eq & vi & Hvi_eq).
    destruct c2 as (Hc0_eq & vj & Hvj_eq).
    subst.

    (**according to the type of eval_pc:
         static unsigned long long get_subl(unsigned long long x1, unsigned long long y1)
       1. return value should be  x+y
       2. the memory is same
      *)
    exists (Val.sub (Vint vi) (Vint vj)), m, Events.E0.

  split_and; unfold step2;auto.
    -
      repeat forward_star.
    - simpl.
      unfold val32_correct. eauto.
    - simpl.
      constructor.
      reflexivity.
    - apply unmodifies_effect_refl.
  Qed.

End Get_sub.

Existing Instance correct_function_get_sub.
