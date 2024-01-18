
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

module Coq__1 = struct
 (** val add : int -> int -> int **)let rec add = (+)
end
include Coq__1

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Stdlib.succ (add p m))
      n0

  (** val mul : int -> int -> int **)

  let rec mul n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n0

  (** val even : int -> bool **)

  let rec even n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun n' -> even n')
        n1)
      n0

  (** val odd : int -> bool **)

  let odd n0 =
    negb (even n0)

  (** val div2 : int -> int **)

  let rec div2 = fun n -> n/2

  (** val bitwise : (bool -> bool -> bool) -> int -> int -> int -> int **)

  let rec bitwise op n0 a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' ->
      add (if op (odd a) (odd b) then Stdlib.succ 0 else 0)
        (mul (Stdlib.succ (Stdlib.succ 0))
          (bitwise op n' (div2 a) (div2 b))))
      n0

  (** val coq_land : int -> int -> int **)

  let coq_land a b =
    bitwise (&&) a a b
 end

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of int
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Stdlib.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val pred_N : int -> int **)

  let pred_N x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> ((fun p->2*p) p))
      (fun p -> (pred_double p))
      (fun _ -> 0)
      x

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos 1
  | IsPos p -> IsPos ((fun p->1+2*p) p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos ((fun p->2*p) p)
  | x0 -> x0

  (** val double_pred_mask : int -> mask **)

  let double_pred_mask x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> IsPos ((fun p->2*p) ((fun p->2*p) p)))
      (fun p -> IsPos ((fun p->2*p) (pred_double p)))
      (fun _ -> IsNul)
      x

  (** val sub_mask : int -> int -> mask **)

  let rec sub_mask x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double_mask (sub_mask p q))
        (fun q -> succ_double_mask (sub_mask p q))
        (fun _ -> IsPos ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> IsNeg)
        (fun _ -> IsNeg)
        (fun _ -> IsNul)
        y)
      x

  (** val sub_mask_carry : int -> int -> mask **)

  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double_mask (sub_mask_carry p q))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun _ -> double_pred_mask p)
        y)
      (fun _ -> IsNeg)
      x

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1 **)

  let rec iter f x n0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n0

  (** val div2 : int -> int **)

  let div2 p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> p0)
      (fun p0 -> p0)
      (fun _ -> 1)
      p

  (** val div2_up : int -> int **)

  let div2_up p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> succ p0)
      (fun p0 -> p0)
      (fun _ -> 1)
      p

  (** val size : int -> int **)

  let rec size p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> succ (size p0))
      (fun p0 -> succ (size p0))
      (fun _ -> 1)
      p

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val eqb : int -> int -> bool **)

  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p

  (** val coq_Nsucc_double : int -> int **)

  let coq_Nsucc_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      x

  (** val coq_Ndouble : int -> int **)

  let coq_Ndouble n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      n0

  (** val coq_lor : int -> int -> int **)

  let rec coq_lor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun _ -> p)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->2*p) (coq_lor p0 q0))
        (fun _ -> (fun p->1+2*p) p0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> q)
        (fun q0 -> (fun p->1+2*p) q0)
        (fun _ -> q)
        q)
      p

  (** val coq_land : int -> int -> int **)

  let rec coq_land p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 1)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 1)
        (fun _ -> 0)
        (fun _ -> 1)
        q)
      p

  (** val ldiff : int -> int -> int **)

  let rec ldiff p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Nsucc_double (ldiff p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun _ -> p)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 0)
        (fun _ -> 1)
        (fun _ -> 0)
        q)
      p

  (** val coq_lxor : int -> int -> int **)

  let rec coq_lxor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun _ -> ((fun p->1+2*p) p0))
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> ((fun p->2*p) q0))
        (fun q0 -> ((fun p->1+2*p) q0))
        (fun _ -> 0)
        q)
      p

  (** val testbit : int -> int -> bool **)

  let rec testbit p n0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun n1 -> testbit p0 (pred_N n1))
        n0)
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> false)
        (fun n1 -> testbit p0 (pred_N n1))
        n0)
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun _ -> false)
        n0)
      p

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Stdlib.succ 0)

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n0

  (** val eq_dec : int -> int -> bool **)

  let rec eq_dec p x0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        (fun _ -> false)
        x0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        x0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        x0)
      p
 end

module N =
 struct
  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      x

  (** val double : int -> int **)

  let double n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      n0

  (** val succ_pos : int -> int **)

  let succ_pos n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> Coq_Pos.succ p)
      n0

  (** val sub : int -> int -> int **)

  let sub = fun n m -> Stdlib.max 0 (n-m)

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val pos_div_eucl : int -> int -> int * int **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> (0, 1))
        (fun p ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ -> (0, 1))
          (fun _ -> (0, 1))
          (fun _ -> (1, 0))
          p)
        b)
      a

  (** val coq_lor : int -> int -> int **)

  let coq_lor n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n0)
        (fun q -> (Coq_Pos.coq_lor p q))
        m)
      n0

  (** val coq_land : int -> int -> int **)

  let coq_land n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> 0)
        (fun q -> Coq_Pos.coq_land p q)
        m)
      n0

  (** val ldiff : int -> int -> int **)

  let ldiff n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n0)
        (fun q -> Coq_Pos.ldiff p q)
        m)
      n0

  (** val coq_lxor : int -> int -> int **)

  let coq_lxor n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n0)
        (fun q -> Coq_Pos.coq_lxor p q)
        m)
      n0

  (** val testbit : int -> int -> bool **)

  let testbit a n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> false)
      (fun p -> Coq_Pos.testbit p n0)
      a
 end

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Coq_Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Coq_Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Coq_Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Coq_Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val pred : int -> int **)

  let pred = Stdlib.pred

  (** val sub : int -> int -> int **)

  let sub = (-)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : int -> int -> bool **)

  let eqb x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun q -> Coq_Pos.eqb p q)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun q -> Coq_Pos.eqb p q)
        y)
      x

  (** val to_nat : int -> int **)

  let to_nat z0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> Coq_Pos.to_nat p)
      (fun _ -> 0)
      z0

  (** val of_nat : int -> int **)

  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n1 -> (Coq_Pos.of_succ_nat n1))
      n0

  (** val of_N : int -> int **)

  let of_N = fun p -> p

  (** val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let iter n0 f x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> x)
      (fun p -> Coq_Pos.iter f x p)
      (fun _ -> x)
      n0

  (** val pos_div_eucl : int -> int -> int * int **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul ((fun p->2*p) 1) r) 1 in
      if ltb r' b
      then ((mul ((fun p->2*p) 1) q), r')
      else ((add (mul ((fun p->2*p) 1) q) 1), (sub r' b)))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul ((fun p->2*p) 1) r in
      if ltb r' b
      then ((mul ((fun p->2*p) 1) q), r')
      else ((add (mul ((fun p->2*p) 1) q) 1), (sub r' b)))
      (fun _ -> if leb ((fun p->2*p) 1) b then (0, 1) else (1, 0))
      a

  (** val div_eucl : int -> int -> int * int **)

  let div_eucl a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (0, 0))
      (fun a' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, 0))
        (fun _ -> pos_div_eucl a' b)
        (fun b' ->
        let (q, r) = pos_div_eucl a' b' in
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ -> ((opp q), 0))
           (fun _ -> ((opp (add q 1)), (add b r)))
           (fun _ -> ((opp (add q 1)), (add b r)))
           r))
        b)
      (fun a' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, 0))
        (fun _ ->
        let (q, r) = pos_div_eucl a' b in
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ -> ((opp q), 0))
           (fun _ -> ((opp (add q 1)), (sub b r)))
           (fun _ -> ((opp (add q 1)), (sub b r)))
           r))
        (fun b' -> let (q, r) = pos_div_eucl a' b' in (q, (opp r)))
        b)
      a

  (** val div : int -> int -> int **)

  let div a b =
    let (q, _) = div_eucl a b in q

  (** val modulo : int -> int -> int **)

  let modulo a b =
    let (_, r) = div_eucl a b in r

  (** val quotrem : int -> int -> int * int **)

  let quotrem a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (0, 0))
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, a))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((of_N q), (of_N r)))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((opp (of_N q)), (of_N r)))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, a))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((opp (of_N q)), (opp (of_N r))))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((of_N q), (opp (of_N r))))
        b)
      a

  (** val quot : int -> int -> int **)

  let quot a b =
    fst (quotrem a b)

  (** val rem : int -> int -> int **)

  let rem a b =
    snd (quotrem a b)

  (** val odd : int -> bool **)

  let odd z0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> false)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> true)
        p)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> true)
        p)
      z0

  (** val div2 : int -> int **)

  let div2 z0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> (Coq_Pos.div2 p))
        (fun _ -> (Coq_Pos.div2 p))
        (fun _ -> 0)
        p)
      (fun p -> (~-) (Coq_Pos.div2_up p))
      z0

  (** val log2 : int -> int **)

  let log2 z0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p -> (Coq_Pos.size p))
        (fun p -> (Coq_Pos.size p))
        (fun _ -> 0)
        p0)
      (fun _ -> 0)
      z0

  (** val testbit : int -> int -> bool **)

  let testbit a n0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> odd a)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun a0 -> Coq_Pos.testbit a0 p)
        (fun a0 -> negb (N.testbit (Coq_Pos.pred_N a0) p))
        a)
      (fun _ -> false)
      n0

  (** val shiftl : int -> int -> int **)

  let shiftl a n0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> a)
      (fun p -> Coq_Pos.iter (mul ((fun p->2*p) 1)) a p)
      (fun p -> Coq_Pos.iter div2 a p)
      n0

  (** val shiftr : int -> int -> int **)

  let shiftr a n0 =
    shiftl a (opp n0)

  (** val coq_lor : int -> int -> int **)

  let coq_lor a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> (Coq_Pos.coq_lor a0 b0))
        (fun b0 -> (~-) (N.succ_pos (N.ldiff (Coq_Pos.pred_N b0) a0)))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> (~-)
        (N.succ_pos (N.ldiff (Coq_Pos.pred_N a0) b0)))
        (fun b0 -> (~-)
        (N.succ_pos (N.coq_land (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
        b)
      a

  (** val coq_land : int -> int -> int **)

  let coq_land a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> 0)
        (fun b0 -> of_N (Coq_Pos.coq_land a0 b0))
        (fun b0 -> of_N (N.ldiff a0 (Coq_Pos.pred_N b0)))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> 0)
        (fun b0 -> of_N (N.ldiff b0 (Coq_Pos.pred_N a0)))
        (fun b0 -> (~-)
        (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
        b)
      a

  (** val coq_lxor : int -> int -> int **)

  let coq_lxor a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> of_N (Coq_Pos.coq_lxor a0 b0))
        (fun b0 -> (~-) (N.succ_pos (N.coq_lxor a0 (Coq_Pos.pred_N b0))))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> (~-)
        (N.succ_pos (N.coq_lxor (Coq_Pos.pred_N a0) b0)))
        (fun b0 -> of_N (N.coq_lxor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0)))
        b)
      a

  (** val eq_dec : int -> int -> bool **)

  let eq_dec x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun x0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun p0 -> Coq_Pos.eq_dec x0 p0)
        (fun _ -> false)
        y)
      (fun x0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun p0 -> Coq_Pos.eq_dec x0 p0)
        y)
      x
 end

(** val z_lt_dec : int -> int -> bool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> true
  | _ -> false

(** val z_le_dec : int -> int -> bool **)

let z_le_dec x y =
  match Z.compare x y with
  | Gt -> false
  | _ -> true

(** val z_le_gt_dec : int -> int -> bool **)

let z_le_gt_dec =
  z_le_dec

(** val nth_error : 'a1 list -> int -> 'a1 option **)

let rec nth_error l n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> None
              | x :: _ -> Some x)
    (fun n1 -> match l with
               | [] -> None
               | _ :: l0 -> nth_error l0 n1)
    n0

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val shift_nat : int -> int -> int **)

let rec shift_nat n0 z0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> z0)
    (fun n1 -> (fun p->2*p) (shift_nat n1 z0))
    n0

(** val shift_pos : int -> int -> int **)

let shift_pos n0 z0 =
  Coq_Pos.iter (fun x -> (fun p->2*p) x) z0 n0

(** val two_power_nat : int -> int **)

let two_power_nat n0 =
  (shift_nat n0 1)

(** val two_power_pos : int -> int **)

let two_power_pos x =
  (shift_pos x 1)

(** val two_p : int -> int **)

let two_p x =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> 1)
    (fun y -> two_power_pos y)
    (fun _ -> 0)
    x

(** val zeq : int -> int -> bool **)

let zeq =
  Z.eq_dec

(** val zlt : int -> int -> bool **)

let zlt =
  z_lt_dec

(** val zle : int -> int -> bool **)

let zle =
  z_le_gt_dec

(** val proj_sumbool : bool -> bool **)

let proj_sumbool = function
| true -> true
| false -> false

(** val p_mod_two_p : int -> int -> int **)

let rec p_mod_two_p p n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun m ->
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun q -> Z.succ_double (p_mod_two_p q m))
      (fun q -> Z.double (p_mod_two_p q m))
      (fun _ -> 1)
      p)
    n0

(** val zshiftin : bool -> int -> int **)

let zshiftin b x =
  if b then Z.succ_double x else Z.double x

(** val zzero_ext : int -> int -> int **)

let zzero_ext n0 x =
  Z.iter n0 (fun rec0 x0 -> zshiftin (Z.odd x0) (rec0 (Z.div2 x0))) (fun _ ->
    0) x

(** val zsign_ext : int -> int -> int **)

let zsign_ext n0 x =
  Z.iter (Z.pred n0) (fun rec0 x0 -> zshiftin (Z.odd x0) (rec0 (Z.div2 x0)))
    (fun x0 ->
    if (&&) (Z.odd x0) (proj_sumbool (zlt 0 n0)) then (~-) 1 else 0) x

(** val z_one_bits : int -> int -> int -> int list **)

let rec z_one_bits n0 x i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun m ->
    if Z.odd x
    then i :: (z_one_bits m (Z.div2 x) (Z.add i 1))
    else z_one_bits m (Z.div2 x) (Z.add i 1))
    n0

(** val p_is_power2 : int -> bool **)

let rec p_is_power2 p =
  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
    (fun _ -> false)
    (fun q -> p_is_power2 q)
    (fun _ -> true)
    p

(** val z_is_power2 : int -> int option **)

let z_is_power2 x =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> None)
    (fun p -> if p_is_power2 p then Some (Z.log2 x) else None)
    (fun _ -> None)
    x

(** val zsize : int -> int **)

let zsize x =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> 0)
    (fun p -> (Coq_Pos.size p))
    (fun _ -> 0)
    x

type comparison0 =
| Ceq
| Cne
| Clt
| Cle
| Cgt
| Cge

module type WORDSIZE =
 sig
  val wordsize : int
 end

module Make =
 functor (WS:WORDSIZE) ->
 struct
  (** val wordsize : int **)

  let wordsize =
    WS.wordsize

  (** val zwordsize : int **)

  let zwordsize =
    Z.of_nat wordsize

  (** val modulus : int **)

  let modulus =
    two_power_nat wordsize

  (** val half_modulus : int **)

  let half_modulus =
    Z.div modulus ((fun p->2*p) 1)

  (** val max_unsigned : int **)

  let max_unsigned =
    Z.sub modulus 1

  (** val max_signed : int **)

  let max_signed =
    Z.sub half_modulus 1

  (** val min_signed : int **)

  let min_signed =
    Z.opp half_modulus

  (** val intval : int -> int **)

  let intval i =
    i

  (** val coq_Z_mod_modulus : int -> int **)

  let coq_Z_mod_modulus x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> p_mod_two_p p wordsize)
      (fun p ->
      let r = p_mod_two_p p wordsize in if zeq r 0 then 0 else Z.sub modulus r)
      x

  (** val unsigned : int -> int **)

  let unsigned =
    intval

  (** val signed : int -> int **)

  let signed n0 =
    let x = unsigned n0 in if zlt x half_modulus then x else Z.sub x modulus

  (** val repr : int -> int **)

  let repr =
    coq_Z_mod_modulus

  (** val zero : int **)

  let zero =
    repr 0

  (** val one : int **)

  let one =
    repr 1

  (** val mone : int **)

  let mone =
    repr ((~-) 1)

  (** val iwordsize : int **)

  let iwordsize =
    repr zwordsize

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    zeq

  (** val eq : int -> int -> bool **)

  let eq x y =
    if zeq (unsigned x) (unsigned y) then true else false

  (** val lt : int -> int -> bool **)

  let lt x y =
    if zlt (signed x) (signed y) then true else false

  (** val ltu : int -> int -> bool **)

  let ltu x y =
    if zlt (unsigned x) (unsigned y) then true else false

  (** val neg : int -> int **)

  let neg x =
    repr (Z.opp (unsigned x))

  (** val add : int -> int -> int **)

  let add x y =
    repr (Z.add (unsigned x) (unsigned y))

  (** val sub : int -> int -> int **)

  let sub x y =
    repr (Z.sub (unsigned x) (unsigned y))

  (** val mul : int -> int -> int **)

  let mul x y =
    repr (Z.mul (unsigned x) (unsigned y))

  (** val divs : int -> int -> int **)

  let divs x y =
    repr (Z.quot (signed x) (signed y))

  (** val mods : int -> int -> int **)

  let mods x y =
    repr (Z.rem (signed x) (signed y))

  (** val divu : int -> int -> int **)

  let divu x y =
    repr (Z.div (unsigned x) (unsigned y))

  (** val modu : int -> int -> int **)

  let modu x y =
    repr (Z.modulo (unsigned x) (unsigned y))

  (** val coq_and : int -> int -> int **)

  let coq_and x y =
    repr (Z.coq_land (unsigned x) (unsigned y))

  (** val coq_or : int -> int -> int **)

  let coq_or x y =
    repr (Z.coq_lor (unsigned x) (unsigned y))

  (** val xor : int -> int -> int **)

  let xor x y =
    repr (Z.coq_lxor (unsigned x) (unsigned y))

  (** val not : int -> int **)

  let not x =
    xor x mone

  (** val shl : int -> int -> int **)

  let shl x y =
    repr (Z.shiftl (unsigned x) (unsigned y))

  (** val shru : int -> int -> int **)

  let shru x y =
    repr (Z.shiftr (unsigned x) (unsigned y))

  (** val shr : int -> int -> int **)

  let shr x y =
    repr (Z.shiftr (signed x) (unsigned y))

  (** val rol : int -> int -> int **)

  let rol x y =
    let n0 = Z.modulo (unsigned y) zwordsize in
    repr
      (Z.coq_lor (Z.shiftl (unsigned x) n0)
        (Z.shiftr (unsigned x) (Z.sub zwordsize n0)))

  (** val ror : int -> int -> int **)

  let ror x y =
    let n0 = Z.modulo (unsigned y) zwordsize in
    repr
      (Z.coq_lor (Z.shiftr (unsigned x) n0)
        (Z.shiftl (unsigned x) (Z.sub zwordsize n0)))

  (** val rolm : int -> int -> int -> int **)

  let rolm x a m =
    coq_and (rol x a) m

  (** val shrx : int -> int -> int **)

  let shrx x y =
    divs x (shl one y)

  (** val mulhu : int -> int -> int **)

  let mulhu x y =
    repr (Z.div (Z.mul (unsigned x) (unsigned y)) modulus)

  (** val mulhs : int -> int -> int **)

  let mulhs x y =
    repr (Z.div (Z.mul (signed x) (signed y)) modulus)

  (** val negative : int -> int **)

  let negative x =
    if lt x zero then one else zero

  (** val add_carry : int -> int -> int -> int **)

  let add_carry x y cin =
    if zlt (Z.add (Z.add (unsigned x) (unsigned y)) (unsigned cin)) modulus
    then zero
    else one

  (** val add_overflow : int -> int -> int -> int **)

  let add_overflow x y cin =
    let s = Z.add (Z.add (signed x) (signed y)) (signed cin) in
    if (&&) (proj_sumbool (zle min_signed s))
         (proj_sumbool (zle s max_signed))
    then zero
    else one

  (** val sub_borrow : int -> int -> int -> int **)

  let sub_borrow x y bin =
    if zlt (Z.sub (Z.sub (unsigned x) (unsigned y)) (unsigned bin)) 0
    then one
    else zero

  (** val sub_overflow : int -> int -> int -> int **)

  let sub_overflow x y bin =
    let s = Z.sub (Z.sub (signed x) (signed y)) (signed bin) in
    if (&&) (proj_sumbool (zle min_signed s))
         (proj_sumbool (zle s max_signed))
    then zero
    else one

  (** val shr_carry : int -> int -> int **)

  let shr_carry x y =
    if (&&) (lt x zero) (negb (eq (coq_and x (sub (shl one y) one)) zero))
    then one
    else zero

  (** val zero_ext : int -> int -> int **)

  let zero_ext n0 x =
    repr (zzero_ext n0 (unsigned x))

  (** val sign_ext : int -> int -> int **)

  let sign_ext n0 x =
    repr (zsign_ext n0 (unsigned x))

  (** val one_bits : int -> int list **)

  let one_bits x =
    map repr (z_one_bits wordsize (unsigned x) 0)

  (** val is_power2 : int -> int option **)

  let is_power2 x =
    match z_is_power2 (unsigned x) with
    | Some i -> Some (repr i)
    | None -> None

  (** val cmp : comparison0 -> int -> int -> bool **)

  let cmp c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> lt x y
    | Cle -> negb (lt y x)
    | Cgt -> lt y x
    | Cge -> negb (lt x y)

  (** val cmpu : comparison0 -> int -> int -> bool **)

  let cmpu c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> ltu x y
    | Cle -> negb (ltu y x)
    | Cgt -> ltu y x
    | Cge -> negb (ltu x y)

  (** val notbool : int -> int **)

  let notbool x =
    if eq x zero then one else zero

  (** val divmodu2 : int -> int -> int -> (int * int) option **)

  let divmodu2 nhi nlo d =
    if eq_dec d zero
    then None
    else let (q, r) =
           Z.div_eucl (Z.add (Z.mul (unsigned nhi) modulus) (unsigned nlo))
             (unsigned d)
         in
         if zle q max_unsigned then Some ((repr q), (repr r)) else None

  (** val divmods2 : int -> int -> int -> (int * int) option **)

  let divmods2 nhi nlo d =
    if eq_dec d zero
    then None
    else let (q, r) =
           Z.quotrem (Z.add (Z.mul (signed nhi) modulus) (unsigned nlo))
             (signed d)
         in
         if (&&) (proj_sumbool (zle min_signed q))
              (proj_sumbool (zle q max_signed))
         then Some ((repr q), (repr r))
         else None

  (** val testbit : int -> int -> bool **)

  let testbit x i =
    Z.testbit (unsigned x) i

  (** val int_of_one_bits : int list -> int **)

  let rec int_of_one_bits = function
  | [] -> zero
  | a :: b -> add (shl one a) (int_of_one_bits b)

  (** val no_overlap : int -> int -> int -> int -> bool **)

  let no_overlap ofs1 sz1 ofs2 sz2 =
    let x1 = unsigned ofs1 in
    let x2 = unsigned ofs2 in
    (&&)
      ((&&) (proj_sumbool (zlt (Z.add x1 sz1) modulus))
        (proj_sumbool (zlt (Z.add x2 sz2) modulus)))
      ((||) (proj_sumbool (zle (Z.add x1 sz1) x2))
        (proj_sumbool (zle (Z.add x2 sz2) x1)))

  (** val size : int -> int **)

  let size x =
    zsize (unsigned x)

  (** val unsigned_bitfield_extract : int -> int -> int -> int **)

  let unsigned_bitfield_extract pos width n0 =
    zero_ext width (shru n0 (repr pos))

  (** val signed_bitfield_extract : int -> int -> int -> int **)

  let signed_bitfield_extract pos width n0 =
    sign_ext width (shru n0 (repr pos))

  (** val bitfield_insert : int -> int -> int -> int -> int **)

  let bitfield_insert pos width n0 p =
    let mask0 = shl (repr (Z.sub (two_p width) 1)) (repr pos) in
    coq_or (shl (zero_ext width p) (repr pos)) (coq_and n0 (not mask0))
 end

module Wordsize_32 =
 struct
  (** val wordsize : int **)

  let wordsize =
    Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      0)))))))))))))))))))))))))))))))
 end

module Int = Make(Wordsize_32)

module Wordsize_64 =
 struct
  (** val wordsize : int **)

  let wordsize =
    Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 end

module Int64 =
 struct
  (** val wordsize : int **)

  let wordsize =
    Wordsize_64.wordsize

  (** val modulus : int **)

  let modulus =
    two_power_nat wordsize

  (** val intval : int -> int **)

  let intval = function
  | intval0 -> intval0

  (** val coq_Z_mod_modulus : int -> int **)

  let coq_Z_mod_modulus x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> p_mod_two_p p wordsize)
      (fun p ->
      let r = p_mod_two_p p wordsize in if zeq r 0 then 0 else Z.sub modulus r)
      x

  (** val unsigned : int -> int **)

  let unsigned =
    intval

  (** val repr : int -> int **)

  let repr x =
    (coq_Z_mod_modulus x)

  (** val coq_and : int -> int -> int **)

  let coq_and x y =
    repr (Z.coq_land (unsigned x) (unsigned y))

  (** val shl : int -> int -> int **)

  let shl x y =
    repr (Z.shiftl (unsigned x) (unsigned y))

  (** val shru : int -> int -> int **)

  let shru x y =
    repr (Z.shiftr (unsigned x) (unsigned y))
 end

type ident = int

type typ =
| Tint
| Tfloat
| Tlong
| Tsingle
| Tany32
| Tany64

type rettype =
| Tret of typ
| Tint8signed
| Tint8unsigned
| Tint16signed
| Tint16unsigned
| Tvoid

type calling_convention = { cc_vararg : int option; cc_unproto : bool;
                            cc_structret : bool }

type signature = { sig_args : typ list; sig_res : rettype;
                   sig_cc : calling_convention }

type ireg =
| IR0
| IR1
| IR2
| IR3
| IR4
| IR5
| IR6
| IR7
| IR8
| IR9
| IR10
| IR11
| IR12
| IR13
| IR14

(** val encode_arm32 : int -> int -> int -> int -> int **)

let encode_arm32 v ins from size0 =
  Int.bitfield_insert (Z.of_nat from) (Z.of_nat size0) ins v

(** val decode_arm32 : int -> int -> int -> int **)

let decode_arm32 ins from size0 =
  Int.unsigned_bitfield_extract (Z.of_nat from) (Z.of_nat size0) ins

type signedness =
| Signed
| Unsigned

(** val int64_to_sint32 : int -> int **)

let int64_to_sint32 x =
  Int.repr (Int64.unsigned x)

(** val get_dst : int -> int **)

let get_dst i =
  Int64.unsigned
    (Int64.shru
      (Int64.coq_and i
        (Int64.repr ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          1)))))))))))))
      (Int64.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))

(** val get_src : int -> int **)

let get_src i =
  Int64.unsigned
    (Int64.shru
      (Int64.coq_and i
        (Int64.repr ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          1)))))))))))))))))
      (Int64.repr ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))

(** val get_opcode : int -> int **)

let get_opcode ins =
  Z.to_nat
    (Int64.unsigned
      (Int64.coq_and ins
        (Int64.repr ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          1))))))))))

(** val get_offset : int -> int **)

let get_offset i =
  Int.sign_ext ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
    (Int.repr
      (Int64.unsigned
        (Int64.shru
          (Int64.shl i
            (Int64.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
              ((fun p->2*p) ((fun p->2*p) 1)))))))
          (Int64.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
            ((fun p->1+2*p) 1)))))))))

(** val get_immediate : int -> int **)

let get_immediate i1 =
  int64_to_sint32
    (Int64.shru i1
      (Int64.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) 1)))))))

type 'a set = 'a list

(** val set_add : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set **)

let rec set_add aeq_dec a = function
| [] -> a :: []
| a1 :: x1 -> if aeq_dec a a1 then a1 :: x1 else a1 :: (set_add aeq_dec a x1)

(** val set_mem : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> bool **)

let rec set_mem aeq_dec a = function
| [] -> false
| a1 :: x1 -> if aeq_dec a a1 then true else set_mem aeq_dec a x1

type breg =
| R0
| R1
| R2
| R3
| R4
| R5
| R6
| R7
| R8
| R9
| R10

type listset = breg set

(** val z_of_breg : breg -> int **)

let z_of_breg = function
| R0 -> 0
| R1 -> 1
| R2 -> ((fun p->2*p) 1)
| R3 -> ((fun p->1+2*p) 1)
| R4 -> ((fun p->2*p) ((fun p->2*p) 1))
| R5 -> ((fun p->1+2*p) ((fun p->2*p) 1))
| R6 -> ((fun p->2*p) ((fun p->1+2*p) 1))
| R7 -> ((fun p->1+2*p) ((fun p->1+2*p) 1))
| R8 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
| R9 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))
| R10 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))

(** val breg_eq : breg -> breg -> bool **)

let breg_eq x y =
  match x with
  | R0 -> (match y with
           | R0 -> true
           | _ -> false)
  | R1 -> (match y with
           | R1 -> true
           | _ -> false)
  | R2 -> (match y with
           | R2 -> true
           | _ -> false)
  | R3 -> (match y with
           | R3 -> true
           | _ -> false)
  | R4 -> (match y with
           | R4 -> true
           | _ -> false)
  | R5 -> (match y with
           | R5 -> true
           | _ -> false)
  | R6 -> (match y with
           | R6 -> true
           | _ -> false)
  | R7 -> (match y with
           | R7 -> true
           | _ -> false)
  | R8 -> (match y with
           | R8 -> true
           | _ -> false)
  | R9 -> (match y with
           | R9 -> true
           | _ -> false)
  | R10 -> (match y with
            | R10 -> true
            | _ -> false)

(** val int_of_breg : breg -> int **)

let int_of_breg i =
  Int.repr (z_of_breg i)

type off = int

type imm = int

type aluOp =
| ADD
| SUB
| MUL
| DIV
| OR
| AND
| LSH
| RSH
| NEG
| MOD
| XOR
| MOV
| ARSH

type cmpOp =
| EQ
| NE
| SET
| GT of signedness
| GE of signedness
| LT of signedness
| LE of signedness

type sizeOp =
| Byte
| HalfWord
| Word

type instruction =
| Pload of sizeOp * breg * breg * off
| Pstore of sizeOp * breg * (breg, imm) sum * off
| Palu32 of aluOp * breg * (breg, imm) sum
| Pjmp of off
| Pjmpcmp of cmpOp * breg * (breg, imm) sum * off
| Pcall of ident * signature
| Pret

type code = int list

type bpf_code = instruction list

type bin_code = int list

(** val get_instruction_alu32_imm :
    breg -> imm -> int -> instruction option **)

let get_instruction_alu32_imm rd i op =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> None)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> None)
        (fun n2 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> None)
          (fun n3 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> Some (Palu32 (ADD, rd, (Inr i))))
            (fun n4 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> None)
              (fun n5 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> None)
                (fun n6 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> None)
                  (fun n7 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> None)
                    (fun n8 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> None)
                      (fun n9 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> None)
                        (fun n10 ->
                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                          (fun _ -> None)
                          (fun n11 ->
                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                            (fun _ -> None)
                            (fun n12 ->
                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                              (fun _ -> None)
                              (fun n13 ->
                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                (fun _ -> None)
                                (fun n14 ->
                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                  (fun _ -> None)
                                  (fun n15 ->
                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                    (fun _ -> None)
                                    (fun n16 ->
                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                      (fun _ -> None)
                                      (fun n17 ->
                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                        (fun _ -> None)
                                        (fun n18 ->
                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                          (fun _ -> None)
                                          (fun n19 ->
                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                            (fun _ -> Some (Palu32 (SUB, rd,
                                            (Inr i))))
                                            (fun n20 ->
                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                              (fun _ -> None)
                                              (fun n21 ->
                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                (fun _ -> None)
                                                (fun n22 ->
                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                  (fun _ -> None)
                                                  (fun n23 ->
                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                    (fun _ ->
                                                    None)
                                                    (fun n24 ->
                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                      (fun _ ->
                                                      None)
                                                      (fun n25 ->
                                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                        (fun _ ->
                                                        None)
                                                        (fun n26 ->
                                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                          (fun _ ->
                                                          None)
                                                          (fun n27 ->
                                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                            (fun _ ->
                                                            None)
                                                            (fun n28 ->
                                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                              (fun _ ->
                                                              None)
                                                              (fun n29 ->
                                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                (fun _ ->
                                                                None)
                                                                (fun n30 ->
                                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                  (fun _ ->
                                                                  None)
                                                                  (fun n31 ->
                                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n32 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n33 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n34 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n35 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (MUL, rd,
                                                                    (Inr
                                                                    i))))
                                                                    (fun n36 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n37 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n38 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n39 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n40 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n41 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n42 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n43 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n44 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n45 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n46 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n47 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n48 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n49 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n50 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n51 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (DIV, rd,
                                                                    (Inr
                                                                    i))))
                                                                    (fun n52 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n53 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n54 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n55 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n56 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n57 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n58 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n59 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n60 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n61 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n62 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n63 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n64 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n65 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n66 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n67 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (OR, rd,
                                                                    (Inr
                                                                    i))))
                                                                    (fun n68 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n69 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n70 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n71 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n72 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n73 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n74 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n75 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n76 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n77 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n78 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n79 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n80 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n81 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n82 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n83 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (AND, rd,
                                                                    (Inr
                                                                    i))))
                                                                    (fun n84 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n85 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n86 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n87 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n88 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n89 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n90 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n91 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n92 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n93 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n94 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n95 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n96 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n97 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n98 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n99 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (LSH, rd,
                                                                    (Inr
                                                                    i))))
                                                                    (fun n100 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n101 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n102 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n103 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n104 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n105 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n106 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n107 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n108 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n109 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n110 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n111 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n112 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n113 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n114 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n115 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (RSH, rd,
                                                                    (Inr
                                                                    i))))
                                                                    (fun n116 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n117 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n118 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n119 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n120 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n121 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n122 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n123 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n124 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n125 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n126 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n127 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n128 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n129 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n130 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n131 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (NEG, rd,
                                                                    (Inl
                                                                    rd))))
                                                                    (fun n132 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n133 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n134 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n135 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n136 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n137 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n138 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n139 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n140 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n141 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n142 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n143 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n144 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n145 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n146 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n147 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (MOD, rd,
                                                                    (Inr
                                                                    i))))
                                                                    (fun n148 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n149 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n150 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n151 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n152 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n153 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n154 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n155 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n156 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n157 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n158 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n159 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n160 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n161 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n162 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n163 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (XOR, rd,
                                                                    (Inr
                                                                    i))))
                                                                    (fun n164 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n165 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n166 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n167 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n168 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n169 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n170 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n171 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n172 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n173 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n174 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n175 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n176 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n177 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n178 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n179 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (MOV, rd,
                                                                    (Inr
                                                                    i))))
                                                                    (fun n180 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n181 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n182 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n183 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n184 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n185 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n186 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n187 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n188 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n189 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n190 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n191 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n192 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n193 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n194 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n195 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (ARSH,
                                                                    rd, (Inr
                                                                    i))))
                                                                    (fun _ ->
                                                                    None)
                                                                    n195)
                                                                    n194)
                                                                    n193)
                                                                    n192)
                                                                    n191)
                                                                    n190)
                                                                    n189)
                                                                    n188)
                                                                    n187)
                                                                    n186)
                                                                    n185)
                                                                    n184)
                                                                    n183)
                                                                    n182)
                                                                    n181)
                                                                    n180)
                                                                    n179)
                                                                    n178)
                                                                    n177)
                                                                    n176)
                                                                    n175)
                                                                    n174)
                                                                    n173)
                                                                    n172)
                                                                    n171)
                                                                    n170)
                                                                    n169)
                                                                    n168)
                                                                    n167)
                                                                    n166)
                                                                    n165)
                                                                    n164)
                                                                    n163)
                                                                    n162)
                                                                    n161)
                                                                    n160)
                                                                    n159)
                                                                    n158)
                                                                    n157)
                                                                    n156)
                                                                    n155)
                                                                    n154)
                                                                    n153)
                                                                    n152)
                                                                    n151)
                                                                    n150)
                                                                    n149)
                                                                    n148)
                                                                    n147)
                                                                    n146)
                                                                    n145)
                                                                    n144)
                                                                    n143)
                                                                    n142)
                                                                    n141)
                                                                    n140)
                                                                    n139)
                                                                    n138)
                                                                    n137)
                                                                    n136)
                                                                    n135)
                                                                    n134)
                                                                    n133)
                                                                    n132)
                                                                    n131)
                                                                    n130)
                                                                    n129)
                                                                    n128)
                                                                    n127)
                                                                    n126)
                                                                    n125)
                                                                    n124)
                                                                    n123)
                                                                    n122)
                                                                    n121)
                                                                    n120)
                                                                    n119)
                                                                    n118)
                                                                    n117)
                                                                    n116)
                                                                    n115)
                                                                    n114)
                                                                    n113)
                                                                    n112)
                                                                    n111)
                                                                    n110)
                                                                    n109)
                                                                    n108)
                                                                    n107)
                                                                    n106)
                                                                    n105)
                                                                    n104)
                                                                    n103)
                                                                    n102)
                                                                    n101)
                                                                    n100)
                                                                    n99)
                                                                    n98)
                                                                    n97)
                                                                    n96)
                                                                    n95)
                                                                    n94)
                                                                    n93)
                                                                    n92)
                                                                    n91)
                                                                    n90)
                                                                    n89)
                                                                    n88)
                                                                    n87)
                                                                    n86)
                                                                    n85)
                                                                    n84)
                                                                    n83)
                                                                    n82)
                                                                    n81)
                                                                    n80)
                                                                    n79)
                                                                    n78)
                                                                    n77)
                                                                    n76)
                                                                    n75)
                                                                    n74)
                                                                    n73)
                                                                    n72)
                                                                    n71)
                                                                    n70)
                                                                    n69)
                                                                    n68)
                                                                    n67)
                                                                    n66)
                                                                    n65)
                                                                    n64)
                                                                    n63)
                                                                    n62)
                                                                    n61)
                                                                    n60)
                                                                    n59)
                                                                    n58)
                                                                    n57)
                                                                    n56)
                                                                    n55)
                                                                    n54)
                                                                    n53)
                                                                    n52)
                                                                    n51)
                                                                    n50)
                                                                    n49)
                                                                    n48)
                                                                    n47)
                                                                    n46)
                                                                    n45)
                                                                    n44)
                                                                    n43)
                                                                    n42)
                                                                    n41)
                                                                    n40)
                                                                    n39)
                                                                    n38)
                                                                    n37)
                                                                    n36)
                                                                    n35)
                                                                    n34)
                                                                    n33)
                                                                    n32)
                                                                    n31)
                                                                  n30)
                                                                n29)
                                                              n28)
                                                            n27)
                                                          n26)
                                                        n25)
                                                      n24)
                                                    n23)
                                                  n22)
                                                n21)
                                              n20)
                                            n19)
                                          n18)
                                        n17)
                                      n16)
                                    n15)
                                  n14)
                                n13)
                              n12)
                            n11)
                          n10)
                        n9)
                      n8)
                    n7)
                  n6)
                n5)
              n4)
            n3)
          n2)
        n1)
      n0)
    op

(** val get_instruction_alu32_reg :
    breg -> breg -> int -> instruction option **)

let get_instruction_alu32_reg rd rs op =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> None)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> None)
        (fun n2 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> None)
          (fun n3 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> None)
            (fun n4 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> None)
              (fun n5 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> None)
                (fun n6 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> None)
                  (fun n7 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> None)
                    (fun n8 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> None)
                      (fun n9 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> None)
                        (fun n10 ->
                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                          (fun _ -> None)
                          (fun n11 ->
                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                            (fun _ -> Some (Palu32 (ADD, rd, (Inl
                            rs))))
                            (fun n12 ->
                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                              (fun _ -> None)
                              (fun n13 ->
                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                (fun _ -> None)
                                (fun n14 ->
                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                  (fun _ -> None)
                                  (fun n15 ->
                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                    (fun _ -> None)
                                    (fun n16 ->
                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                      (fun _ -> None)
                                      (fun n17 ->
                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                        (fun _ -> None)
                                        (fun n18 ->
                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                          (fun _ -> None)
                                          (fun n19 ->
                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                            (fun _ -> None)
                                            (fun n20 ->
                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                              (fun _ -> None)
                                              (fun n21 ->
                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                (fun _ -> None)
                                                (fun n22 ->
                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                  (fun _ -> None)
                                                  (fun n23 ->
                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                    (fun _ ->
                                                    None)
                                                    (fun n24 ->
                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                      (fun _ ->
                                                      None)
                                                      (fun n25 ->
                                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                        (fun _ ->
                                                        None)
                                                        (fun n26 ->
                                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                          (fun _ ->
                                                          None)
                                                          (fun n27 ->
                                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                            (fun _ -> Some
                                                            (Palu32 (SUB, rd,
                                                            (Inl
                                                            rs))))
                                                            (fun n28 ->
                                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                              (fun _ ->
                                                              None)
                                                              (fun n29 ->
                                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                (fun _ ->
                                                                None)
                                                                (fun n30 ->
                                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                  (fun _ ->
                                                                  None)
                                                                  (fun n31 ->
                                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n32 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n33 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n34 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n35 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n36 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n37 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n38 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n39 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n40 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n41 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n42 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n43 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (MUL, rd,
                                                                    (Inl
                                                                    rs))))
                                                                    (fun n44 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n45 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n46 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n47 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n48 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n49 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n50 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n51 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n52 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n53 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n54 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n55 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n56 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n57 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n58 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n59 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (DIV, rd,
                                                                    (Inl
                                                                    rs))))
                                                                    (fun n60 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n61 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n62 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n63 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n64 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n65 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n66 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n67 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n68 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n69 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n70 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n71 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n72 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n73 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n74 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n75 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (OR, rd,
                                                                    (Inl
                                                                    rs))))
                                                                    (fun n76 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n77 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n78 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n79 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n80 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n81 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n82 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n83 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n84 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n85 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n86 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n87 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n88 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n89 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n90 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n91 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (AND, rd,
                                                                    (Inl
                                                                    rs))))
                                                                    (fun n92 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n93 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n94 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n95 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n96 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n97 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n98 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n99 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n100 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n101 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n102 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n103 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n104 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n105 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n106 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n107 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (LSH, rd,
                                                                    (Inl
                                                                    rs))))
                                                                    (fun n108 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n109 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n110 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n111 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n112 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n113 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n114 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n115 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n116 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n117 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n118 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n119 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n120 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n121 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n122 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n123 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (RSH, rd,
                                                                    (Inl
                                                                    rs))))
                                                                    (fun n124 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n125 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n126 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n127 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n128 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n129 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n130 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n131 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n132 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n133 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n134 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n135 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n136 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n137 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n138 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n139 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n140 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n141 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n142 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n143 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n144 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n145 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n146 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n147 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n148 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n149 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n150 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n151 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n152 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n153 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n154 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n155 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (MOD, rd,
                                                                    (Inl
                                                                    rs))))
                                                                    (fun n156 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n157 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n158 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n159 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n160 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n161 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n162 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n163 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n164 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n165 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n166 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n167 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n168 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n169 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n170 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n171 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (XOR, rd,
                                                                    (Inl
                                                                    rs))))
                                                                    (fun n172 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n173 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n174 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n175 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n176 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n177 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n178 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n179 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n180 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n181 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n182 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n183 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n184 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n185 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n186 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n187 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (MOV, rd,
                                                                    (Inl
                                                                    rs))))
                                                                    (fun n188 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n189 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n190 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n191 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n192 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n193 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n194 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n195 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n196 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n197 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n198 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n199 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n200 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n201 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n202 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n203 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Palu32
                                                                    (ARSH,
                                                                    rd, (Inl
                                                                    rs))))
                                                                    (fun _ ->
                                                                    None)
                                                                    n203)
                                                                    n202)
                                                                    n201)
                                                                    n200)
                                                                    n199)
                                                                    n198)
                                                                    n197)
                                                                    n196)
                                                                    n195)
                                                                    n194)
                                                                    n193)
                                                                    n192)
                                                                    n191)
                                                                    n190)
                                                                    n189)
                                                                    n188)
                                                                    n187)
                                                                    n186)
                                                                    n185)
                                                                    n184)
                                                                    n183)
                                                                    n182)
                                                                    n181)
                                                                    n180)
                                                                    n179)
                                                                    n178)
                                                                    n177)
                                                                    n176)
                                                                    n175)
                                                                    n174)
                                                                    n173)
                                                                    n172)
                                                                    n171)
                                                                    n170)
                                                                    n169)
                                                                    n168)
                                                                    n167)
                                                                    n166)
                                                                    n165)
                                                                    n164)
                                                                    n163)
                                                                    n162)
                                                                    n161)
                                                                    n160)
                                                                    n159)
                                                                    n158)
                                                                    n157)
                                                                    n156)
                                                                    n155)
                                                                    n154)
                                                                    n153)
                                                                    n152)
                                                                    n151)
                                                                    n150)
                                                                    n149)
                                                                    n148)
                                                                    n147)
                                                                    n146)
                                                                    n145)
                                                                    n144)
                                                                    n143)
                                                                    n142)
                                                                    n141)
                                                                    n140)
                                                                    n139)
                                                                    n138)
                                                                    n137)
                                                                    n136)
                                                                    n135)
                                                                    n134)
                                                                    n133)
                                                                    n132)
                                                                    n131)
                                                                    n130)
                                                                    n129)
                                                                    n128)
                                                                    n127)
                                                                    n126)
                                                                    n125)
                                                                    n124)
                                                                    n123)
                                                                    n122)
                                                                    n121)
                                                                    n120)
                                                                    n119)
                                                                    n118)
                                                                    n117)
                                                                    n116)
                                                                    n115)
                                                                    n114)
                                                                    n113)
                                                                    n112)
                                                                    n111)
                                                                    n110)
                                                                    n109)
                                                                    n108)
                                                                    n107)
                                                                    n106)
                                                                    n105)
                                                                    n104)
                                                                    n103)
                                                                    n102)
                                                                    n101)
                                                                    n100)
                                                                    n99)
                                                                    n98)
                                                                    n97)
                                                                    n96)
                                                                    n95)
                                                                    n94)
                                                                    n93)
                                                                    n92)
                                                                    n91)
                                                                    n90)
                                                                    n89)
                                                                    n88)
                                                                    n87)
                                                                    n86)
                                                                    n85)
                                                                    n84)
                                                                    n83)
                                                                    n82)
                                                                    n81)
                                                                    n80)
                                                                    n79)
                                                                    n78)
                                                                    n77)
                                                                    n76)
                                                                    n75)
                                                                    n74)
                                                                    n73)
                                                                    n72)
                                                                    n71)
                                                                    n70)
                                                                    n69)
                                                                    n68)
                                                                    n67)
                                                                    n66)
                                                                    n65)
                                                                    n64)
                                                                    n63)
                                                                    n62)
                                                                    n61)
                                                                    n60)
                                                                    n59)
                                                                    n58)
                                                                    n57)
                                                                    n56)
                                                                    n55)
                                                                    n54)
                                                                    n53)
                                                                    n52)
                                                                    n51)
                                                                    n50)
                                                                    n49)
                                                                    n48)
                                                                    n47)
                                                                    n46)
                                                                    n45)
                                                                    n44)
                                                                    n43)
                                                                    n42)
                                                                    n41)
                                                                    n40)
                                                                    n39)
                                                                    n38)
                                                                    n37)
                                                                    n36)
                                                                    n35)
                                                                    n34)
                                                                    n33)
                                                                    n32)
                                                                    n31)
                                                                  n30)
                                                                n29)
                                                              n28)
                                                            n27)
                                                          n26)
                                                        n25)
                                                      n24)
                                                    n23)
                                                  n22)
                                                n21)
                                              n20)
                                            n19)
                                          n18)
                                        n17)
                                      n16)
                                    n15)
                                  n14)
                                n13)
                              n12)
                            n11)
                          n10)
                        n9)
                      n8)
                    n7)
                  n6)
                n5)
              n4)
            n3)
          n2)
        n1)
      n0)
    op

(** val get_instruction_ldx :
    breg -> breg -> off -> int -> instruction option **)

let get_instruction_ldx rd rs ofs op =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> None)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> None)
        (fun n2 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> None)
          (fun n3 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> None)
            (fun n4 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> None)
              (fun n5 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> None)
                (fun n6 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> None)
                  (fun n7 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> None)
                    (fun n8 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> None)
                      (fun n9 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> None)
                        (fun n10 ->
                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                          (fun _ -> None)
                          (fun n11 ->
                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                            (fun _ -> None)
                            (fun n12 ->
                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                              (fun _ -> None)
                              (fun n13 ->
                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                (fun _ -> None)
                                (fun n14 ->
                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                  (fun _ -> None)
                                  (fun n15 ->
                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                    (fun _ -> None)
                                    (fun n16 ->
                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                      (fun _ -> None)
                                      (fun n17 ->
                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                        (fun _ -> None)
                                        (fun n18 ->
                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                          (fun _ -> None)
                                          (fun n19 ->
                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                            (fun _ -> None)
                                            (fun n20 ->
                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                              (fun _ -> None)
                                              (fun n21 ->
                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                (fun _ -> None)
                                                (fun n22 ->
                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                  (fun _ -> None)
                                                  (fun n23 ->
                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                    (fun _ ->
                                                    None)
                                                    (fun n24 ->
                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                      (fun _ ->
                                                      None)
                                                      (fun n25 ->
                                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                        (fun _ ->
                                                        None)
                                                        (fun n26 ->
                                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                          (fun _ ->
                                                          None)
                                                          (fun n27 ->
                                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                            (fun _ ->
                                                            None)
                                                            (fun n28 ->
                                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                              (fun _ ->
                                                              None)
                                                              (fun n29 ->
                                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                (fun _ ->
                                                                None)
                                                                (fun n30 ->
                                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                  (fun _ ->
                                                                  None)
                                                                  (fun n31 ->
                                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n32 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n33 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n34 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n35 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n36 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n37 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n38 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n39 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n40 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n41 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n42 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n43 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n44 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n45 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n46 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n47 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n48 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n49 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n50 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n51 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n52 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n53 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n54 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n55 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n56 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n57 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n58 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n59 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n60 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n61 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n62 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n63 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n64 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n65 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n66 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n67 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n68 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n69 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n70 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n71 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n72 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n73 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n74 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n75 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n76 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n77 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n78 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n79 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n80 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n81 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n82 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n83 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n84 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n85 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n86 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n87 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n88 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n89 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n90 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n91 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n92 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n93 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n94 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n95 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n96 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pload
                                                                    (Word,
                                                                    rd, rs,
                                                                    ofs)))
                                                                    (fun n97 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n98 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n99 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n100 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n101 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n102 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n103 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n104 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pload
                                                                    (HalfWord,
                                                                    rd, rs,
                                                                    ofs)))
                                                                    (fun n105 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n106 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n107 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n108 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n109 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n110 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n111 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n112 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pload
                                                                    (Byte,
                                                                    rd, rs,
                                                                    ofs)))
                                                                    (fun _ ->
                                                                    None)
                                                                    n112)
                                                                    n111)
                                                                    n110)
                                                                    n109)
                                                                    n108)
                                                                    n107)
                                                                    n106)
                                                                    n105)
                                                                    n104)
                                                                    n103)
                                                                    n102)
                                                                    n101)
                                                                    n100)
                                                                    n99)
                                                                    n98)
                                                                    n97)
                                                                    n96)
                                                                    n95)
                                                                    n94)
                                                                    n93)
                                                                    n92)
                                                                    n91)
                                                                    n90)
                                                                    n89)
                                                                    n88)
                                                                    n87)
                                                                    n86)
                                                                    n85)
                                                                    n84)
                                                                    n83)
                                                                    n82)
                                                                    n81)
                                                                    n80)
                                                                    n79)
                                                                    n78)
                                                                    n77)
                                                                    n76)
                                                                    n75)
                                                                    n74)
                                                                    n73)
                                                                    n72)
                                                                    n71)
                                                                    n70)
                                                                    n69)
                                                                    n68)
                                                                    n67)
                                                                    n66)
                                                                    n65)
                                                                    n64)
                                                                    n63)
                                                                    n62)
                                                                    n61)
                                                                    n60)
                                                                    n59)
                                                                    n58)
                                                                    n57)
                                                                    n56)
                                                                    n55)
                                                                    n54)
                                                                    n53)
                                                                    n52)
                                                                    n51)
                                                                    n50)
                                                                    n49)
                                                                    n48)
                                                                    n47)
                                                                    n46)
                                                                    n45)
                                                                    n44)
                                                                    n43)
                                                                    n42)
                                                                    n41)
                                                                    n40)
                                                                    n39)
                                                                    n38)
                                                                    n37)
                                                                    n36)
                                                                    n35)
                                                                    n34)
                                                                    n33)
                                                                    n32)
                                                                    n31)
                                                                  n30)
                                                                n29)
                                                              n28)
                                                            n27)
                                                          n26)
                                                        n25)
                                                      n24)
                                                    n23)
                                                  n22)
                                                n21)
                                              n20)
                                            n19)
                                          n18)
                                        n17)
                                      n16)
                                    n15)
                                  n14)
                                n13)
                              n12)
                            n11)
                          n10)
                        n9)
                      n8)
                    n7)
                  n6)
                n5)
              n4)
            n3)
          n2)
        n1)
      n0)
    (Nat.coq_land op (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val get_instruction_st :
    breg -> off -> int -> int -> instruction option **)

let get_instruction_st rd ofs i op =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> None)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> None)
        (fun n2 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> None)
          (fun n3 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> None)
            (fun n4 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> None)
              (fun n5 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> None)
                (fun n6 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> None)
                  (fun n7 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> None)
                    (fun n8 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> None)
                      (fun n9 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> None)
                        (fun n10 ->
                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                          (fun _ -> None)
                          (fun n11 ->
                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                            (fun _ -> None)
                            (fun n12 ->
                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                              (fun _ -> None)
                              (fun n13 ->
                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                (fun _ -> None)
                                (fun n14 ->
                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                  (fun _ -> None)
                                  (fun n15 ->
                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                    (fun _ -> None)
                                    (fun n16 ->
                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                      (fun _ -> None)
                                      (fun n17 ->
                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                        (fun _ -> None)
                                        (fun n18 ->
                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                          (fun _ -> None)
                                          (fun n19 ->
                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                            (fun _ -> None)
                                            (fun n20 ->
                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                              (fun _ -> None)
                                              (fun n21 ->
                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                (fun _ -> None)
                                                (fun n22 ->
                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                  (fun _ -> None)
                                                  (fun n23 ->
                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                    (fun _ ->
                                                    None)
                                                    (fun n24 ->
                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                      (fun _ ->
                                                      None)
                                                      (fun n25 ->
                                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                        (fun _ ->
                                                        None)
                                                        (fun n26 ->
                                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                          (fun _ ->
                                                          None)
                                                          (fun n27 ->
                                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                            (fun _ ->
                                                            None)
                                                            (fun n28 ->
                                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                              (fun _ ->
                                                              None)
                                                              (fun n29 ->
                                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                (fun _ ->
                                                                None)
                                                                (fun n30 ->
                                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                  (fun _ ->
                                                                  None)
                                                                  (fun n31 ->
                                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n32 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n33 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n34 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n35 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n36 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n37 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n38 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n39 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n40 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n41 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n42 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n43 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n44 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n45 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n46 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n47 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n48 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n49 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n50 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n51 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n52 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n53 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n54 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n55 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n56 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n57 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n58 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n59 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n60 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n61 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n62 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n63 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n64 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n65 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n66 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n67 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n68 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n69 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n70 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n71 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n72 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n73 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n74 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n75 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n76 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n77 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n78 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n79 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n80 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n81 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n82 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n83 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n84 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n85 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n86 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n87 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n88 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n89 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n90 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n91 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n92 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n93 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n94 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n95 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n96 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n97 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pstore
                                                                    (Word,
                                                                    rd, (Inr
                                                                    i),
                                                                    ofs)))
                                                                    (fun n98 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n99 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n100 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n101 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n102 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n103 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n104 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n105 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pstore
                                                                    (HalfWord,
                                                                    rd, (Inr
                                                                    i),
                                                                    ofs)))
                                                                    (fun n106 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n107 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n108 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n109 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n110 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n111 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n112 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n113 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pstore
                                                                    (Byte,
                                                                    rd, (Inr
                                                                    i),
                                                                    ofs)))
                                                                    (fun _ ->
                                                                    None)
                                                                    n113)
                                                                    n112)
                                                                    n111)
                                                                    n110)
                                                                    n109)
                                                                    n108)
                                                                    n107)
                                                                    n106)
                                                                    n105)
                                                                    n104)
                                                                    n103)
                                                                    n102)
                                                                    n101)
                                                                    n100)
                                                                    n99)
                                                                    n98)
                                                                    n97)
                                                                    n96)
                                                                    n95)
                                                                    n94)
                                                                    n93)
                                                                    n92)
                                                                    n91)
                                                                    n90)
                                                                    n89)
                                                                    n88)
                                                                    n87)
                                                                    n86)
                                                                    n85)
                                                                    n84)
                                                                    n83)
                                                                    n82)
                                                                    n81)
                                                                    n80)
                                                                    n79)
                                                                    n78)
                                                                    n77)
                                                                    n76)
                                                                    n75)
                                                                    n74)
                                                                    n73)
                                                                    n72)
                                                                    n71)
                                                                    n70)
                                                                    n69)
                                                                    n68)
                                                                    n67)
                                                                    n66)
                                                                    n65)
                                                                    n64)
                                                                    n63)
                                                                    n62)
                                                                    n61)
                                                                    n60)
                                                                    n59)
                                                                    n58)
                                                                    n57)
                                                                    n56)
                                                                    n55)
                                                                    n54)
                                                                    n53)
                                                                    n52)
                                                                    n51)
                                                                    n50)
                                                                    n49)
                                                                    n48)
                                                                    n47)
                                                                    n46)
                                                                    n45)
                                                                    n44)
                                                                    n43)
                                                                    n42)
                                                                    n41)
                                                                    n40)
                                                                    n39)
                                                                    n38)
                                                                    n37)
                                                                    n36)
                                                                    n35)
                                                                    n34)
                                                                    n33)
                                                                    n32)
                                                                    n31)
                                                                  n30)
                                                                n29)
                                                              n28)
                                                            n27)
                                                          n26)
                                                        n25)
                                                      n24)
                                                    n23)
                                                  n22)
                                                n21)
                                              n20)
                                            n19)
                                          n18)
                                        n17)
                                      n16)
                                    n15)
                                  n14)
                                n13)
                              n12)
                            n11)
                          n10)
                        n9)
                      n8)
                    n7)
                  n6)
                n5)
              n4)
            n3)
          n2)
        n1)
      n0)
    (Nat.coq_land op (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val get_instruction_stx :
    breg -> breg -> off -> int -> instruction option **)

let get_instruction_stx rd rs ofs op =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> None)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> None)
        (fun n2 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> None)
          (fun n3 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> None)
            (fun n4 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> None)
              (fun n5 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> None)
                (fun n6 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> None)
                  (fun n7 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> None)
                    (fun n8 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> None)
                      (fun n9 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> None)
                        (fun n10 ->
                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                          (fun _ -> None)
                          (fun n11 ->
                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                            (fun _ -> None)
                            (fun n12 ->
                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                              (fun _ -> None)
                              (fun n13 ->
                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                (fun _ -> None)
                                (fun n14 ->
                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                  (fun _ -> None)
                                  (fun n15 ->
                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                    (fun _ -> None)
                                    (fun n16 ->
                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                      (fun _ -> None)
                                      (fun n17 ->
                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                        (fun _ -> None)
                                        (fun n18 ->
                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                          (fun _ -> None)
                                          (fun n19 ->
                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                            (fun _ -> None)
                                            (fun n20 ->
                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                              (fun _ -> None)
                                              (fun n21 ->
                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                (fun _ -> None)
                                                (fun n22 ->
                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                  (fun _ -> None)
                                                  (fun n23 ->
                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                    (fun _ ->
                                                    None)
                                                    (fun n24 ->
                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                      (fun _ ->
                                                      None)
                                                      (fun n25 ->
                                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                        (fun _ ->
                                                        None)
                                                        (fun n26 ->
                                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                          (fun _ ->
                                                          None)
                                                          (fun n27 ->
                                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                            (fun _ ->
                                                            None)
                                                            (fun n28 ->
                                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                              (fun _ ->
                                                              None)
                                                              (fun n29 ->
                                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                (fun _ ->
                                                                None)
                                                                (fun n30 ->
                                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                  (fun _ ->
                                                                  None)
                                                                  (fun n31 ->
                                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n32 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n33 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n34 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n35 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n36 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n37 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n38 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n39 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n40 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n41 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n42 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n43 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n44 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n45 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n46 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n47 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n48 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n49 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n50 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n51 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n52 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n53 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n54 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n55 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n56 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n57 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n58 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n59 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n60 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n61 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n62 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n63 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n64 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n65 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n66 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n67 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n68 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n69 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n70 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n71 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n72 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n73 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n74 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n75 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n76 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n77 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n78 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n79 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n80 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n81 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n82 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n83 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n84 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n85 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n86 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n87 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n88 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n89 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n90 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n91 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n92 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n93 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n94 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n95 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n96 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n97 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n98 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pstore
                                                                    (Word,
                                                                    rd, (Inl
                                                                    rs),
                                                                    ofs)))
                                                                    (fun n99 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n100 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n101 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n102 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n103 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n104 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n105 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n106 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pstore
                                                                    (HalfWord,
                                                                    rd, (Inl
                                                                    rs),
                                                                    ofs)))
                                                                    (fun n107 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n108 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n109 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n110 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n111 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n112 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n113 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n114 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pstore
                                                                    (Byte,
                                                                    rd, (Inl
                                                                    rs),
                                                                    ofs)))
                                                                    (fun _ ->
                                                                    None)
                                                                    n114)
                                                                    n113)
                                                                    n112)
                                                                    n111)
                                                                    n110)
                                                                    n109)
                                                                    n108)
                                                                    n107)
                                                                    n106)
                                                                    n105)
                                                                    n104)
                                                                    n103)
                                                                    n102)
                                                                    n101)
                                                                    n100)
                                                                    n99)
                                                                    n98)
                                                                    n97)
                                                                    n96)
                                                                    n95)
                                                                    n94)
                                                                    n93)
                                                                    n92)
                                                                    n91)
                                                                    n90)
                                                                    n89)
                                                                    n88)
                                                                    n87)
                                                                    n86)
                                                                    n85)
                                                                    n84)
                                                                    n83)
                                                                    n82)
                                                                    n81)
                                                                    n80)
                                                                    n79)
                                                                    n78)
                                                                    n77)
                                                                    n76)
                                                                    n75)
                                                                    n74)
                                                                    n73)
                                                                    n72)
                                                                    n71)
                                                                    n70)
                                                                    n69)
                                                                    n68)
                                                                    n67)
                                                                    n66)
                                                                    n65)
                                                                    n64)
                                                                    n63)
                                                                    n62)
                                                                    n61)
                                                                    n60)
                                                                    n59)
                                                                    n58)
                                                                    n57)
                                                                    n56)
                                                                    n55)
                                                                    n54)
                                                                    n53)
                                                                    n52)
                                                                    n51)
                                                                    n50)
                                                                    n49)
                                                                    n48)
                                                                    n47)
                                                                    n46)
                                                                    n45)
                                                                    n44)
                                                                    n43)
                                                                    n42)
                                                                    n41)
                                                                    n40)
                                                                    n39)
                                                                    n38)
                                                                    n37)
                                                                    n36)
                                                                    n35)
                                                                    n34)
                                                                    n33)
                                                                    n32)
                                                                    n31)
                                                                  n30)
                                                                n29)
                                                              n28)
                                                            n27)
                                                          n26)
                                                        n25)
                                                      n24)
                                                    n23)
                                                  n22)
                                                n21)
                                              n20)
                                            n19)
                                          n18)
                                        n17)
                                      n16)
                                    n15)
                                  n14)
                                n13)
                              n12)
                            n11)
                          n10)
                        n9)
                      n8)
                    n7)
                  n6)
                n5)
              n4)
            n3)
          n2)
        n1)
      n0)
    (Nat.coq_land op (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val get_instruction_branch_imm :
    breg -> off -> imm -> int -> instruction option **)

let get_instruction_branch_imm rd ofs i op =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> None)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> None)
        (fun n2 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> None)
          (fun n3 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> None)
            (fun n4 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> Some (Pjmp ofs))
              (fun n5 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> None)
                (fun n6 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> None)
                  (fun n7 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> None)
                    (fun n8 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> None)
                      (fun n9 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> None)
                        (fun n10 ->
                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                          (fun _ -> None)
                          (fun n11 ->
                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                            (fun _ -> None)
                            (fun n12 ->
                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                              (fun _ -> None)
                              (fun n13 ->
                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                (fun _ -> None)
                                (fun n14 ->
                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                  (fun _ -> None)
                                  (fun n15 ->
                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                    (fun _ -> None)
                                    (fun n16 ->
                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                      (fun _ -> None)
                                      (fun n17 ->
                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                        (fun _ -> None)
                                        (fun n18 ->
                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                          (fun _ -> None)
                                          (fun n19 ->
                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                            (fun _ -> None)
                                            (fun n20 ->
                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                              (fun _ -> Some (Pjmpcmp (EQ,
                                              rd, (Inr i), ofs)))
                                              (fun n21 ->
                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                (fun _ -> None)
                                                (fun n22 ->
                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                  (fun _ -> None)
                                                  (fun n23 ->
                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                    (fun _ ->
                                                    None)
                                                    (fun n24 ->
                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                      (fun _ ->
                                                      None)
                                                      (fun n25 ->
                                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                        (fun _ ->
                                                        None)
                                                        (fun n26 ->
                                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                          (fun _ ->
                                                          None)
                                                          (fun n27 ->
                                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                            (fun _ ->
                                                            None)
                                                            (fun n28 ->
                                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                              (fun _ ->
                                                              None)
                                                              (fun n29 ->
                                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                (fun _ ->
                                                                None)
                                                                (fun n30 ->
                                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                  (fun _ ->
                                                                  None)
                                                                  (fun n31 ->
                                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n32 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n33 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n34 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n35 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n36 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    ((GT
                                                                    Unsigned),
                                                                    rd, (Inr
                                                                    i),
                                                                    ofs)))
                                                                    (fun n37 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n38 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n39 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n40 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n41 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n42 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n43 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n44 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n45 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n46 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n47 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n48 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n49 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n50 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n51 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n52 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    ((GE
                                                                    Unsigned),
                                                                    rd, (Inr
                                                                    i),
                                                                    ofs)))
                                                                    (fun n53 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n54 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n55 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n56 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n57 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n58 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n59 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n60 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n61 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n62 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n63 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n64 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n65 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n66 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n67 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n68 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    (SET, rd,
                                                                    (Inr i),
                                                                    ofs)))
                                                                    (fun n69 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n70 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n71 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n72 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n73 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n74 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n75 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n76 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n77 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n78 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n79 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n80 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n81 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n82 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n83 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n84 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    (NE, rd,
                                                                    (Inr i),
                                                                    ofs)))
                                                                    (fun n85 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n86 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n87 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n88 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n89 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n90 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n91 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n92 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n93 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n94 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n95 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n96 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n97 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n98 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n99 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n100 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    ((GT
                                                                    Signed),
                                                                    rd, (Inr
                                                                    i),
                                                                    ofs)))
                                                                    (fun n101 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n102 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n103 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n104 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n105 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n106 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n107 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n108 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n109 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n110 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n111 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n112 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n113 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n114 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n115 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n116 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    ((GE
                                                                    Signed),
                                                                    rd, (Inr
                                                                    i),
                                                                    ofs)))
                                                                    (fun n117 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n118 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n119 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n120 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n121 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n122 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n123 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n124 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n125 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n126 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n127 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n128 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n129 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n130 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n131 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n132 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n133 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n134 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n135 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n136 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n137 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n138 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n139 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n140 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n141 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n142 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n143 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n144 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n145 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n146 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n147 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n148 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    Pret)
                                                                    (fun n149 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n150 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n151 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n152 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n153 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n154 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n155 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n156 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n157 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n158 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n159 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n160 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n161 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n162 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n163 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n164 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    ((LT
                                                                    Unsigned),
                                                                    rd, (Inr
                                                                    i),
                                                                    ofs)))
                                                                    (fun n165 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n166 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n167 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n168 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n169 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n170 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n171 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n172 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n173 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n174 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n175 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n176 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n177 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n178 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n179 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n180 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    ((LE
                                                                    Unsigned),
                                                                    rd, (Inr
                                                                    i),
                                                                    ofs)))
                                                                    (fun n181 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n182 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n183 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n184 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n185 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n186 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n187 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n188 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n189 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n190 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n191 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n192 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n193 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n194 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n195 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n196 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    ((LT
                                                                    Signed),
                                                                    rd, (Inr
                                                                    i),
                                                                    ofs)))
                                                                    (fun n197 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n198 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n199 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n200 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n201 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n202 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n203 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n204 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n205 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n206 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n207 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n208 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n209 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n210 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n211 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n212 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    ((LE
                                                                    Signed),
                                                                    rd, (Inr
                                                                    i),
                                                                    ofs)))
                                                                    (fun _ ->
                                                                    None)
                                                                    n212)
                                                                    n211)
                                                                    n210)
                                                                    n209)
                                                                    n208)
                                                                    n207)
                                                                    n206)
                                                                    n205)
                                                                    n204)
                                                                    n203)
                                                                    n202)
                                                                    n201)
                                                                    n200)
                                                                    n199)
                                                                    n198)
                                                                    n197)
                                                                    n196)
                                                                    n195)
                                                                    n194)
                                                                    n193)
                                                                    n192)
                                                                    n191)
                                                                    n190)
                                                                    n189)
                                                                    n188)
                                                                    n187)
                                                                    n186)
                                                                    n185)
                                                                    n184)
                                                                    n183)
                                                                    n182)
                                                                    n181)
                                                                    n180)
                                                                    n179)
                                                                    n178)
                                                                    n177)
                                                                    n176)
                                                                    n175)
                                                                    n174)
                                                                    n173)
                                                                    n172)
                                                                    n171)
                                                                    n170)
                                                                    n169)
                                                                    n168)
                                                                    n167)
                                                                    n166)
                                                                    n165)
                                                                    n164)
                                                                    n163)
                                                                    n162)
                                                                    n161)
                                                                    n160)
                                                                    n159)
                                                                    n158)
                                                                    n157)
                                                                    n156)
                                                                    n155)
                                                                    n154)
                                                                    n153)
                                                                    n152)
                                                                    n151)
                                                                    n150)
                                                                    n149)
                                                                    n148)
                                                                    n147)
                                                                    n146)
                                                                    n145)
                                                                    n144)
                                                                    n143)
                                                                    n142)
                                                                    n141)
                                                                    n140)
                                                                    n139)
                                                                    n138)
                                                                    n137)
                                                                    n136)
                                                                    n135)
                                                                    n134)
                                                                    n133)
                                                                    n132)
                                                                    n131)
                                                                    n130)
                                                                    n129)
                                                                    n128)
                                                                    n127)
                                                                    n126)
                                                                    n125)
                                                                    n124)
                                                                    n123)
                                                                    n122)
                                                                    n121)
                                                                    n120)
                                                                    n119)
                                                                    n118)
                                                                    n117)
                                                                    n116)
                                                                    n115)
                                                                    n114)
                                                                    n113)
                                                                    n112)
                                                                    n111)
                                                                    n110)
                                                                    n109)
                                                                    n108)
                                                                    n107)
                                                                    n106)
                                                                    n105)
                                                                    n104)
                                                                    n103)
                                                                    n102)
                                                                    n101)
                                                                    n100)
                                                                    n99)
                                                                    n98)
                                                                    n97)
                                                                    n96)
                                                                    n95)
                                                                    n94)
                                                                    n93)
                                                                    n92)
                                                                    n91)
                                                                    n90)
                                                                    n89)
                                                                    n88)
                                                                    n87)
                                                                    n86)
                                                                    n85)
                                                                    n84)
                                                                    n83)
                                                                    n82)
                                                                    n81)
                                                                    n80)
                                                                    n79)
                                                                    n78)
                                                                    n77)
                                                                    n76)
                                                                    n75)
                                                                    n74)
                                                                    n73)
                                                                    n72)
                                                                    n71)
                                                                    n70)
                                                                    n69)
                                                                    n68)
                                                                    n67)
                                                                    n66)
                                                                    n65)
                                                                    n64)
                                                                    n63)
                                                                    n62)
                                                                    n61)
                                                                    n60)
                                                                    n59)
                                                                    n58)
                                                                    n57)
                                                                    n56)
                                                                    n55)
                                                                    n54)
                                                                    n53)
                                                                    n52)
                                                                    n51)
                                                                    n50)
                                                                    n49)
                                                                    n48)
                                                                    n47)
                                                                    n46)
                                                                    n45)
                                                                    n44)
                                                                    n43)
                                                                    n42)
                                                                    n41)
                                                                    n40)
                                                                    n39)
                                                                    n38)
                                                                    n37)
                                                                    n36)
                                                                    n35)
                                                                    n34)
                                                                    n33)
                                                                    n32)
                                                                    n31)
                                                                  n30)
                                                                n29)
                                                              n28)
                                                            n27)
                                                          n26)
                                                        n25)
                                                      n24)
                                                    n23)
                                                  n22)
                                                n21)
                                              n20)
                                            n19)
                                          n18)
                                        n17)
                                      n16)
                                    n15)
                                  n14)
                                n13)
                              n12)
                            n11)
                          n10)
                        n9)
                      n8)
                    n7)
                  n6)
                n5)
              n4)
            n3)
          n2)
        n1)
      n0)
    op

(** val get_instruction_branch_reg :
    breg -> breg -> off -> int -> instruction option **)

let get_instruction_branch_reg rd rs ofs op =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> None)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> None)
        (fun n2 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> None)
          (fun n3 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> None)
            (fun n4 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> None)
              (fun n5 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> None)
                (fun n6 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> None)
                  (fun n7 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> None)
                    (fun n8 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> None)
                      (fun n9 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> None)
                        (fun n10 ->
                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                          (fun _ -> None)
                          (fun n11 ->
                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                            (fun _ -> None)
                            (fun n12 ->
                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                              (fun _ -> None)
                              (fun n13 ->
                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                (fun _ -> None)
                                (fun n14 ->
                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                  (fun _ -> None)
                                  (fun n15 ->
                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                    (fun _ -> None)
                                    (fun n16 ->
                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                      (fun _ -> None)
                                      (fun n17 ->
                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                        (fun _ -> None)
                                        (fun n18 ->
                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                          (fun _ -> None)
                                          (fun n19 ->
                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                            (fun _ -> None)
                                            (fun n20 ->
                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                              (fun _ -> None)
                                              (fun n21 ->
                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                (fun _ -> None)
                                                (fun n22 ->
                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                  (fun _ -> None)
                                                  (fun n23 ->
                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                    (fun _ ->
                                                    None)
                                                    (fun n24 ->
                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                      (fun _ ->
                                                      None)
                                                      (fun n25 ->
                                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                        (fun _ ->
                                                        None)
                                                        (fun n26 ->
                                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                          (fun _ ->
                                                          None)
                                                          (fun n27 ->
                                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                            (fun _ ->
                                                            None)
                                                            (fun n28 ->
                                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                              (fun _ -> Some
                                                              (Pjmpcmp (EQ,
                                                              rd, (Inl rs),
                                                              ofs)))
                                                              (fun n29 ->
                                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                (fun _ ->
                                                                None)
                                                                (fun n30 ->
                                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                  (fun _ ->
                                                                  None)
                                                                  (fun n31 ->
                                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n32 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n33 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n34 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n35 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n36 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n37 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n38 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n39 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n40 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n41 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n42 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n43 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n44 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    ((GT
                                                                    Unsigned),
                                                                    rd, (Inl
                                                                    rs),
                                                                    ofs)))
                                                                    (fun n45 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n46 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n47 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n48 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n49 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n50 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n51 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n52 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n53 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n54 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n55 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n56 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n57 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n58 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n59 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n60 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    ((GE
                                                                    Unsigned),
                                                                    rd, (Inl
                                                                    rs),
                                                                    ofs)))
                                                                    (fun n61 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n62 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n63 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n64 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n65 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n66 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n67 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n68 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n69 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n70 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n71 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n72 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n73 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n74 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n75 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n76 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    (SET, rd,
                                                                    (Inl rs),
                                                                    ofs)))
                                                                    (fun n77 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n78 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n79 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n80 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n81 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n82 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n83 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n84 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n85 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n86 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n87 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n88 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n89 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n90 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n91 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n92 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    (NE, rd,
                                                                    (Inl rs),
                                                                    ofs)))
                                                                    (fun n93 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n94 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n95 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n96 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n97 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n98 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n99 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n100 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n101 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n102 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n103 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n104 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n105 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n106 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n107 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n108 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    ((GT
                                                                    Signed),
                                                                    rd, (Inl
                                                                    rs),
                                                                    ofs)))
                                                                    (fun n109 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n110 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n111 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n112 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n113 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n114 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n115 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n116 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n117 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n118 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n119 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n120 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n121 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n122 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n123 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n124 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    ((GE
                                                                    Signed),
                                                                    rd, (Inl
                                                                    rs),
                                                                    ofs)))
                                                                    (fun n125 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n126 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n127 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n128 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n129 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n130 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n131 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n132 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n133 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n134 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n135 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n136 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n137 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n138 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n139 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n140 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n141 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n142 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n143 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n144 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n145 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n146 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n147 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n148 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n149 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n150 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n151 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n152 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n153 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n154 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n155 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n156 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n157 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n158 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n159 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n160 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n161 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n162 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n163 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n164 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n165 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n166 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n167 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n168 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n169 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n170 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n171 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n172 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    ((LT
                                                                    Unsigned),
                                                                    rd, (Inl
                                                                    rs),
                                                                    ofs)))
                                                                    (fun n173 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n174 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n175 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n176 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n177 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n178 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n179 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n180 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n181 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n182 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n183 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n184 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n185 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n186 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n187 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n188 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    ((LE
                                                                    Unsigned),
                                                                    rd, (Inl
                                                                    rs),
                                                                    ofs)))
                                                                    (fun n189 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n190 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n191 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n192 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n193 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n194 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n195 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n196 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n197 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n198 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n199 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n200 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n201 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n202 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n203 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n204 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    ((LT
                                                                    Signed),
                                                                    rd, (Inl
                                                                    rs),
                                                                    ofs)))
                                                                    (fun n205 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n206 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n207 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n208 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n209 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n210 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n211 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n212 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n213 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n214 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n215 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n216 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n217 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n218 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n219 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n220 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    (Pjmpcmp
                                                                    ((LE
                                                                    Signed),
                                                                    rd, (Inl
                                                                    rs),
                                                                    ofs)))
                                                                    (fun _ ->
                                                                    None)
                                                                    n220)
                                                                    n219)
                                                                    n218)
                                                                    n217)
                                                                    n216)
                                                                    n215)
                                                                    n214)
                                                                    n213)
                                                                    n212)
                                                                    n211)
                                                                    n210)
                                                                    n209)
                                                                    n208)
                                                                    n207)
                                                                    n206)
                                                                    n205)
                                                                    n204)
                                                                    n203)
                                                                    n202)
                                                                    n201)
                                                                    n200)
                                                                    n199)
                                                                    n198)
                                                                    n197)
                                                                    n196)
                                                                    n195)
                                                                    n194)
                                                                    n193)
                                                                    n192)
                                                                    n191)
                                                                    n190)
                                                                    n189)
                                                                    n188)
                                                                    n187)
                                                                    n186)
                                                                    n185)
                                                                    n184)
                                                                    n183)
                                                                    n182)
                                                                    n181)
                                                                    n180)
                                                                    n179)
                                                                    n178)
                                                                    n177)
                                                                    n176)
                                                                    n175)
                                                                    n174)
                                                                    n173)
                                                                    n172)
                                                                    n171)
                                                                    n170)
                                                                    n169)
                                                                    n168)
                                                                    n167)
                                                                    n166)
                                                                    n165)
                                                                    n164)
                                                                    n163)
                                                                    n162)
                                                                    n161)
                                                                    n160)
                                                                    n159)
                                                                    n158)
                                                                    n157)
                                                                    n156)
                                                                    n155)
                                                                    n154)
                                                                    n153)
                                                                    n152)
                                                                    n151)
                                                                    n150)
                                                                    n149)
                                                                    n148)
                                                                    n147)
                                                                    n146)
                                                                    n145)
                                                                    n144)
                                                                    n143)
                                                                    n142)
                                                                    n141)
                                                                    n140)
                                                                    n139)
                                                                    n138)
                                                                    n137)
                                                                    n136)
                                                                    n135)
                                                                    n134)
                                                                    n133)
                                                                    n132)
                                                                    n131)
                                                                    n130)
                                                                    n129)
                                                                    n128)
                                                                    n127)
                                                                    n126)
                                                                    n125)
                                                                    n124)
                                                                    n123)
                                                                    n122)
                                                                    n121)
                                                                    n120)
                                                                    n119)
                                                                    n118)
                                                                    n117)
                                                                    n116)
                                                                    n115)
                                                                    n114)
                                                                    n113)
                                                                    n112)
                                                                    n111)
                                                                    n110)
                                                                    n109)
                                                                    n108)
                                                                    n107)
                                                                    n106)
                                                                    n105)
                                                                    n104)
                                                                    n103)
                                                                    n102)
                                                                    n101)
                                                                    n100)
                                                                    n99)
                                                                    n98)
                                                                    n97)
                                                                    n96)
                                                                    n95)
                                                                    n94)
                                                                    n93)
                                                                    n92)
                                                                    n91)
                                                                    n90)
                                                                    n89)
                                                                    n88)
                                                                    n87)
                                                                    n86)
                                                                    n85)
                                                                    n84)
                                                                    n83)
                                                                    n82)
                                                                    n81)
                                                                    n80)
                                                                    n79)
                                                                    n78)
                                                                    n77)
                                                                    n76)
                                                                    n75)
                                                                    n74)
                                                                    n73)
                                                                    n72)
                                                                    n71)
                                                                    n70)
                                                                    n69)
                                                                    n68)
                                                                    n67)
                                                                    n66)
                                                                    n65)
                                                                    n64)
                                                                    n63)
                                                                    n62)
                                                                    n61)
                                                                    n60)
                                                                    n59)
                                                                    n58)
                                                                    n57)
                                                                    n56)
                                                                    n55)
                                                                    n54)
                                                                    n53)
                                                                    n52)
                                                                    n51)
                                                                    n50)
                                                                    n49)
                                                                    n48)
                                                                    n47)
                                                                    n46)
                                                                    n45)
                                                                    n44)
                                                                    n43)
                                                                    n42)
                                                                    n41)
                                                                    n40)
                                                                    n39)
                                                                    n38)
                                                                    n37)
                                                                    n36)
                                                                    n35)
                                                                    n34)
                                                                    n33)
                                                                    n32)
                                                                    n31)
                                                                  n30)
                                                                n29)
                                                              n28)
                                                            n27)
                                                          n26)
                                                        n25)
                                                      n24)
                                                    n23)
                                                  n22)
                                                n21)
                                              n20)
                                            n19)
                                          n18)
                                        n17)
                                      n16)
                                    n15)
                                  n14)
                                n13)
                              n12)
                            n11)
                          n10)
                        n9)
                      n8)
                    n7)
                  n6)
                n5)
              n4)
            n3)
          n2)
        n1)
      n0)
    op

(** val z_to_breg : int -> breg option **)

let z_to_breg z0 =
  if Z.eqb z0 0
  then Some R0
  else if Z.eqb z0 1
       then Some R1
       else if Z.eqb z0 ((fun p->2*p) 1)
            then Some R2
            else if Z.eqb z0 ((fun p->1+2*p) 1)
                 then Some R3
                 else if Z.eqb z0 ((fun p->2*p) ((fun p->2*p) 1))
                      then Some R4
                      else if Z.eqb z0 ((fun p->1+2*p) ((fun p->2*p) 1))
                           then Some R5
                           else if Z.eqb z0 ((fun p->2*p) ((fun p->1+2*p) 1))
                                then Some R6
                                else if Z.eqb z0 ((fun p->1+2*p)
                                          ((fun p->1+2*p) 1))
                                     then Some R7
                                     else if Z.eqb z0 ((fun p->2*p)
                                               ((fun p->2*p) ((fun p->2*p)
                                               1)))
                                          then Some R8
                                          else if Z.eqb z0 ((fun p->1+2*p)
                                                    ((fun p->2*p)
                                                    ((fun p->2*p) 1)))
                                               then Some R9
                                               else if Z.eqb z0 ((fun p->2*p)
                                                         ((fun p->1+2*p)
                                                         ((fun p->2*p) 1)))
                                                    then Some R10
                                                    else None

(** val int64_to_dst_breg : int -> breg option **)

let int64_to_dst_breg ins =
  z_to_breg (get_dst ins)

(** val int64_to_src_breg : int -> breg option **)

let int64_to_src_breg ins =
  z_to_breg (get_src ins)

(** val decode_ind : int -> instruction option **)

let decode_ind ins =
  let opcode = get_opcode ins in
  (match int64_to_dst_breg ins with
   | Some dst ->
     let opc =
       Nat.coq_land opcode (Stdlib.succ (Stdlib.succ (Stdlib.succ
         (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
         0)))))))
     in
     let n_ofs = get_offset ins in
     let n_imm = get_immediate ins in
     ((fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> None)
        (fun n0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          match int64_to_src_breg ins with
          | Some src -> get_instruction_ldx dst src n_ofs opcode
          | None -> None)
          (fun n1 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> get_instruction_st dst n_ofs n_imm opcode)
            (fun n2 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ ->
              match int64_to_src_breg ins with
              | Some src -> get_instruction_stx dst src n_ofs opcode
              | None -> None)
              (fun n3 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ ->
                if Int.eq Int.zero
                     (Int.coq_and (Int.repr (Z.of_nat opcode))
                       (Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
                         1)))))
                then get_instruction_alu32_imm dst n_imm opcode
                else (match int64_to_src_breg ins with
                      | Some src -> get_instruction_alu32_reg dst src opcode
                      | None -> None))
                (fun n4 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ ->
                  if Int.eq Int.zero
                       (Int.coq_and (Int.repr (Z.of_nat opcode))
                         (Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
                           1)))))
                  then get_instruction_branch_imm dst n_ofs n_imm opcode
                  else (match int64_to_src_breg ins with
                        | Some src ->
                          get_instruction_branch_reg dst src n_ofs opcode
                        | None -> None))
                  (fun _ -> None)
                  n4)
                n3)
              n2)
            n1)
          n0)
        opc)
   | None -> None)

(** val find_instr : int -> code -> instruction option **)

let find_instr pos c =
  match nth_error c pos with
  | Some ins -> decode_ind ins
  | None -> None

(** val is_alu32 : instruction -> bool **)

let is_alu32 = function
| Palu32 (_, _, _) -> true
| _ -> false

(** val get_alu32_list : code -> int -> int -> bpf_code option **)

let rec get_alu32_list c fuel pc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n0 ->
    match nth_error c pc with
    | Some ins ->
      (match decode_ind ins with
       | Some bpf_ins ->
         if is_alu32 bpf_ins
         then (match get_alu32_list c n0 (Stdlib.succ pc) with
               | Some tl -> Some (bpf_ins :: tl)
               | None -> None)
         else Some []
       | None -> None)
    | None -> None)
    fuel

(** val analyzer_aux : code -> int -> int -> (int * bpf_code) list option **)

let rec analyzer_aux c fuel pc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some [])
    (fun n0 ->
    if (=) (length c) pc
    then Some []
    else (match find_instr pc c with
          | Some bpf_ins ->
            (match bpf_ins with
             | Palu32 (_, _, _) ->
               (match get_alu32_list c (sub (length c) pc) pc with
                | Some l1 ->
                  (match analyzer_aux c n0 (add pc (length l1)) with
                   | Some l -> Some ((pc, l1) :: l)
                   | None -> None)
                | None -> None)
             | Pjmp ofs ->
               let lbl =
                 Z.to_nat
                   (Int.signed
                     (Int.add Int.one (Int.add (Int.repr (Z.of_nat pc)) ofs)))
               in
               (match find_instr lbl c with
                | Some ins ->
                  (match ins with
                   | Palu32 (_, _, _) ->
                     (match get_alu32_list c (sub (length c) lbl) lbl with
                      | Some l1 ->
                        (match analyzer_aux c n0 (Stdlib.succ pc) with
                         | Some l -> Some ((lbl, l1) :: l)
                         | None -> None)
                      | None -> None)
                   | _ -> analyzer_aux c n0 (Stdlib.succ pc))
                | None -> None)
             | Pjmpcmp (_, _, _, ofs) ->
               let lbl =
                 Z.to_nat
                   (Int.signed
                     (Int.add Int.one (Int.add (Int.repr (Z.of_nat pc)) ofs)))
               in
               (match find_instr lbl c with
                | Some ins ->
                  (match ins with
                   | Palu32 (_, _, _) ->
                     (match get_alu32_list c (sub (length c) lbl) lbl with
                      | Some l1 ->
                        (match analyzer_aux c n0 (Stdlib.succ pc) with
                         | Some l -> Some ((lbl, l1) :: l)
                         | None -> None)
                      | None -> None)
                   | _ -> analyzer_aux c n0 (Stdlib.succ pc))
                | None -> None)
             | _ -> analyzer_aux c n0 (Stdlib.succ pc))
          | None -> None))
    fuel

(** val analyzer : code -> (int * bpf_code) list option **)

let analyzer c =
  analyzer_aux c (length c) 0

(** val rbpf_arm_callee_save : listset **)

let rbpf_arm_callee_save =
  R4 :: (R5 :: (R6 :: (R7 :: (R8 :: (R9 :: (R10 :: []))))))

(** val reg_ireg_eqb : breg -> ireg -> bool **)

let reg_ireg_eqb r0 r1 =
  match r0 with
  | R0 -> (match r1 with
           | IR0 -> true
           | _ -> false)
  | R1 -> (match r1 with
           | IR1 -> true
           | _ -> false)
  | R2 -> (match r1 with
           | IR2 -> true
           | _ -> false)
  | R3 -> (match r1 with
           | IR3 -> true
           | _ -> false)
  | R4 -> (match r1 with
           | IR4 -> true
           | _ -> false)
  | R5 -> (match r1 with
           | IR5 -> true
           | _ -> false)
  | R6 -> (match r1 with
           | IR6 -> true
           | _ -> false)
  | R7 -> (match r1 with
           | IR7 -> true
           | _ -> false)
  | R8 -> (match r1 with
           | IR8 -> true
           | _ -> false)
  | R9 -> (match r1 with
           | IR9 -> true
           | _ -> false)
  | R10 -> (match r1 with
            | IR10 -> true
            | _ -> false)

(** val ireg_of_breg : breg -> ireg **)

let ireg_of_breg = function
| R0 -> IR0
| R1 -> IR1
| R2 -> IR2
| R3 -> IR3
| R4 -> IR4
| R5 -> IR5
| R6 -> IR6
| R7 -> IR7
| R8 -> IR8
| R9 -> IR9
| R10 -> IR10

(** val z_of_ireg : ireg -> int **)

let z_of_ireg = function
| IR0 -> 0
| IR1 -> 1
| IR2 -> ((fun p->2*p) 1)
| IR3 -> ((fun p->1+2*p) 1)
| IR4 -> ((fun p->2*p) ((fun p->2*p) 1))
| IR5 -> ((fun p->1+2*p) ((fun p->2*p) 1))
| IR6 -> ((fun p->2*p) ((fun p->1+2*p) 1))
| IR7 -> ((fun p->1+2*p) ((fun p->1+2*p) 1))
| IR8 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
| IR9 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))
| IR10 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))
| IR11 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))
| IR12 -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))
| IR13 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))
| IR14 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))

(** val int_of_ireg : ireg -> int **)

let int_of_ireg r =
  Int.repr (z_of_ireg r)

(** val nOP_OP : int **)

let nOP_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->2*p) 1)))))))))))))))

(** val aDD_R_OP : int **)

let aDD_R_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    1))))))))))))))

(** val aDD_I_OP : int **)

let aDD_I_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) 1)))))))))))))))

(** val aND_R_OP : int **)

let aND_R_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))))

(** val aND_I_OP : int **)

let aND_I_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) 1)))))))))))))))

(** val aSR_R_OP : int **)

let aSR_R_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))))

(** val eOR_R_OP : int **)

let eOR_R_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))))

(** val eOR_I_OP : int **)

let eOR_I_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) 1)))))))))))))))

(** val lSL_R_OP : int **)

let lSL_R_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))))

(** val lSR_R_OP : int **)

let lSR_R_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))))

(** val mOVW_OP : int **)

let mOVW_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))))

(** val mOVT_OP : int **)

let mOVT_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))))

(** val mOV_R_OP : int **)

let mOV_R_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    1))))))))))))))

(** val mUL_OP : int **)

let mUL_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))))

(** val oRR_R_OP : int **)

let oRR_R_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))))

(** val oRR_I_OP : int **)

let oRR_I_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) 1)))))))))))))))

(** val sUB_R_OP : int **)

let sUB_R_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))))

(** val sUB_I_OP : int **)

let sUB_I_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))))

(** val rSB_I_OP : int **)

let rSB_I_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))))

(** val uDIV_LO_OP : int **)

let uDIV_LO_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))))

(** val uDIV_HI_OP : int **)

let uDIV_HI_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))))

(** val bX_OP : int **)

let bX_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    1))))))))))))))

(** val lDR_I_OP : int **)

let lDR_I_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))))

(** val sTR_I_OP : int **)

let sTR_I_OP =
  Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))))))))))

(** val insert : listset -> breg -> listset **)

let rec insert l a =
  match l with
  | [] -> a :: []
  | hd :: tl ->
    if Z.ltb (z_of_breg a) (z_of_breg hd)
    then a :: l
    else if Z.eqb (z_of_breg a) (z_of_breg hd) then l else hd :: (insert tl a)

(** val sort_listset : listset -> listset **)

let rec sort_listset = function
| [] -> []
| hd :: tl -> insert (sort_listset tl) hd

(** val jit_alu32_thumb_mem_template_jit : int -> int -> int -> int -> int **)

let jit_alu32_thumb_mem_template_jit op rt rn imm12 =
  let str_low =
    encode_arm32 rn op 0 (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ 0))))
  in
  let str_high =
    encode_arm32 rt imm12 (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ 0)))))))))))) (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ 0))))
  in
  encode_arm32 str_high str_low (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ 0)))))))))))))))) (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))))))))))))))

(** val jit_alu32_pre : bin_code **)

let jit_alu32_pre =
  let ins_rdn =
    encode_arm32 (Int.repr ((fun p->2*p) ((fun p->2*p) 1))) mOV_R_OP 0
      (Stdlib.succ (Stdlib.succ (Stdlib.succ 0)))
  in
  let ins_rm =
    encode_arm32 Int.one ins_rdn (Stdlib.succ (Stdlib.succ
      (Stdlib.succ 0))) (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ 0))))
  in
  let ins =
    encode_arm32 Int.one ins_rm (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ 0))))))) (Stdlib.succ 0)
  in
  let ins32 =
    encode_arm32 ins nOP_OP (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ 0)))))))))))))))) (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))))))))))))))
  in
  let str =
    jit_alu32_thumb_mem_template_jit sTR_I_OP
      (Int.repr ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))
      (int_of_ireg IR13)
      (Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
        ((fun p->2*p) 1))))))
  in
  ins32 :: (str :: [])

(** val jit_call_save_add : breg -> listset -> bin_code **)

let jit_call_save_add r ls =
  if set_mem breg_eq r ls
  then []
  else let ldr_ins =
         jit_alu32_thumb_mem_template_jit lDR_I_OP (int_of_breg r)
           (int_of_ireg IR12)
           (Int.mul (int_of_breg r)
             (Int.repr ((fun p->2*p) ((fun p->2*p) 1))))
       in
       if set_mem breg_eq r rbpf_arm_callee_save
       then let str_ins =
              jit_alu32_thumb_mem_template_jit sTR_I_OP (int_of_breg r)
                (int_of_ireg IR13)
                (Int.mul (int_of_breg r)
                  (Int.repr ((fun p->2*p) ((fun p->2*p) 1))))
            in
            str_ins :: (ldr_ins :: [])
       else ldr_ins :: []

(** val jit_call_save_reg :
    breg -> breg -> listset -> listset -> (bin_code * listset) * listset **)

let jit_call_save_reg dst src ld_set st_set =
  let l1 = jit_call_save_add dst ld_set in
  let ld_set1 = set_add breg_eq dst ld_set in
  let st_set1 = set_add breg_eq dst st_set in
  let l2 = jit_call_save_add src ld_set1 in
  let ld_set2 = set_add breg_eq src ld_set1 in
  (((app l1 l2), ld_set2), st_set1)

(** val jit_call_save_imm :
    breg -> listset -> listset -> (bin_code * listset) * listset **)

let jit_call_save_imm dst ld_set st_set =
  let l1 = jit_call_save_add dst ld_set in
  ((l1, (set_add breg_eq dst ld_set)), (set_add breg_eq dst st_set))

(** val bpf_alu32_to_thumb_reg_comm : int -> breg -> ireg -> int **)

let bpf_alu32_to_thumb_reg_comm op dst src =
  let ins_lo =
    encode_arm32 (int_of_breg dst) op 0 (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ 0))))
  in
  let ins_hi =
    encode_arm32 (int_of_breg dst) (int_of_ireg src) (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))))))
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      0))))
  in
  encode_arm32 ins_hi ins_lo (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ 0)))))))))))))))) (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))))))))))))))

(** val bpf_alu32_to_thumb_reg : aluOp -> breg -> ireg -> bin_code option **)

let bpf_alu32_to_thumb_reg op dst src =
  match op with
  | ADD ->
    let d =
      if Int.lt (int_of_breg dst)
           (Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
      then Int.zero
      else Int.one
    in
    let rdn =
      if Int.lt (int_of_breg dst)
           (Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
      then int_of_breg dst
      else Int.sub (int_of_breg dst)
             (Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
    in
    let ins_rdn =
      encode_arm32 rdn aDD_R_OP 0 (Stdlib.succ (Stdlib.succ
        (Stdlib.succ 0)))
    in
    let ins_rm =
      encode_arm32 (int_of_ireg src) ins_rdn (Stdlib.succ
        (Stdlib.succ (Stdlib.succ 0))) (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))
    in
    let ins =
      encode_arm32 d ins_rm (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ 0))))))) (Stdlib.succ 0)
    in
    let ins32 =
      encode_arm32 ins nOP_OP (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ 0)))))))))))))))) (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))))))))))))))
    in
    Some (ins32 :: [])
  | SUB -> Some ((bpf_alu32_to_thumb_reg_comm sUB_R_OP dst src) :: [])
  | MUL ->
    let ins_lo =
      encode_arm32 (int_of_breg dst) mUL_OP 0 (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))
    in
    let ins_hi0 =
      encode_arm32 (int_of_breg dst) (int_of_ireg src) (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))))))
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        0))))
    in
    let ins_hi =
      encode_arm32
        (Int.repr ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))
        ins_hi0 (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ 0)))))))))))) (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ 0))))
    in
    let ins32 =
      encode_arm32 ins_hi ins_lo (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ 0)))))))))))))))) (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))))))))))))))
    in
    Some (ins32 :: [])
  | OR -> Some ((bpf_alu32_to_thumb_reg_comm oRR_R_OP dst src) :: [])
  | AND -> Some ((bpf_alu32_to_thumb_reg_comm aND_R_OP dst src) :: [])
  | XOR -> Some ((bpf_alu32_to_thumb_reg_comm eOR_R_OP dst src) :: [])
  | MOV ->
    if reg_ireg_eqb dst src
    then Some []
    else let d =
           if Int.lt (int_of_breg dst)
                (Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
           then Int.zero
           else Int.one
         in
         let rdn =
           if Int.lt (int_of_breg dst)
                (Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
           then int_of_breg dst
           else Int.sub (int_of_breg dst)
                  (Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
         in
         let ins_rdn =
           encode_arm32 rdn mOV_R_OP 0 (Stdlib.succ (Stdlib.succ
             (Stdlib.succ 0)))
         in
         let ins_rm =
           encode_arm32 (int_of_ireg src) ins_rdn (Stdlib.succ
             (Stdlib.succ (Stdlib.succ 0))) (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))
         in
         let ins =
           encode_arm32 d ins_rm (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ 0))))))) (Stdlib.succ 0)
         in
         let ins32 =
           encode_arm32 ins nOP_OP (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ 0))))))))))))))))
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ 0))))))))))))))))
         in
         Some (ins32 :: [])
  | _ -> None

(** val mov_int_to_movwt : int -> ireg -> int -> int **)

let mov_int_to_movwt i r op =
  let lo_imm8 =
    decode_arm32 i 0 (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ 0))))))))
  in
  let lo_imm3 =
    decode_arm32 i (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ 0)))))))) (Stdlib.succ (Stdlib.succ
      (Stdlib.succ 0)))
  in
  let lo_i =
    decode_arm32 i (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      0))))))))))) (Stdlib.succ 0)
  in
  let lo_imm4 =
    decode_arm32 i (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ 0)))))))))))) (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ 0))))
  in
  let movw_lo_0 =
    encode_arm32 lo_imm4 op 0 (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ 0))))
  in
  let movw_lo =
    encode_arm32 lo_i movw_lo_0 (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      0)))))))))) (Stdlib.succ 0)
  in
  let movw_hi_0 =
    encode_arm32 (int_of_ireg r) lo_imm8 (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ 0)))))))) (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))
  in
  let movw_hi =
    encode_arm32 lo_imm3 movw_hi_0 (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ 0)))))))))))) (Stdlib.succ
      (Stdlib.succ (Stdlib.succ 0)))
  in
  encode_arm32 movw_hi movw_lo (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ 0)))))))))))))))) (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))))))))))))))

(** val bpf_alu32_to_thumb_imm_comm :
    int -> aluOp -> breg -> int -> bin_code option **)

let bpf_alu32_to_thumb_imm_comm op alu_op dst imm32 =
  if (&&) (Int.cmpu Cle Int.zero imm32)
       (Int.cmpu Cle imm32
         (Int.repr ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
           ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
           1)))))))))
  then let ins_lo =
         encode_arm32 (int_of_breg dst) op 0 (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))
       in
       let ins_hi =
         encode_arm32 (int_of_breg dst) imm32 (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ 0)))))))) (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ 0))))
       in
       let ins32 =
         encode_arm32 ins_hi ins_lo (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ 0))))))))))))))))
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ 0))))))))))))))))
       in
       Some (ins32 :: [])
  else let lo_32 =
         decode_arm32 imm32 0 (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ 0))))))))))))))))
       in
       let hi_32 =
         decode_arm32 imm32 (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ 0))))))))))))))))
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ 0))))))))))))))))
       in
       if Int.eq lo_32 imm32
       then (match bpf_alu32_to_thumb_reg alu_op dst IR11 with
             | Some l -> Some ((mov_int_to_movwt lo_32 IR11 mOVW_OP) :: l)
             | None -> None)
       else (match bpf_alu32_to_thumb_reg alu_op dst IR11 with
             | Some l ->
               Some
                 ((mov_int_to_movwt lo_32 IR11 mOVW_OP) :: ((mov_int_to_movwt
                                                              hi_32 IR11
                                                              mOVT_OP) :: l))
             | None -> None)

(** val bpf_alu32_to_thumb_imm_shift_comm :
    int -> breg -> int -> bin_code option **)

let bpf_alu32_to_thumb_imm_shift_comm op dst imm32 =
  if (&&) (Int.cmpu Cle Int.zero imm32)
       (Int.cmpu Clt imm32
         (Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
           ((fun p->2*p) 1)))))))
  then let ins_lo =
         encode_arm32 (int_of_breg dst) op 0 (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))
       in
       let ins_hi0 =
         encode_arm32 (int_of_breg dst) (int_of_ireg IR11) (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ 0)))))))) (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ 0))))
       in
       let ins_hi =
         encode_arm32
           (Int.repr ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))
           ins_hi0 (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))))))))))
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ 0))))
       in
       let ins32 =
         encode_arm32 ins_hi ins_lo (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ 0))))))))))))))))
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ 0))))))))))))))))
       in
       Some ((mov_int_to_movwt imm32 IR11 mOVW_OP) :: (ins32 :: []))
  else None

(** val bpf_alu32_to_thumb_imm : aluOp -> breg -> int -> bin_code option **)

let bpf_alu32_to_thumb_imm op dst imm32 =
  match op with
  | ADD -> bpf_alu32_to_thumb_imm_comm aDD_I_OP ADD dst imm32
  | SUB -> bpf_alu32_to_thumb_imm_comm sUB_I_OP SUB dst imm32
  | MUL ->
    let lo_32 =
      decode_arm32 imm32 0 (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ 0))))))))))))))))
    in
    let hi_32 =
      decode_arm32 imm32 (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ 0)))))))))))))))) (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ 0))))))))))))))))
    in
    if Int.eq lo_32 imm32
    then (match bpf_alu32_to_thumb_reg MUL dst IR11 with
          | Some l -> Some ((mov_int_to_movwt lo_32 IR11 mOVW_OP) :: l)
          | None -> None)
    else (match bpf_alu32_to_thumb_reg MUL dst IR11 with
          | Some l ->
            Some
              ((mov_int_to_movwt lo_32 IR11 mOVW_OP) :: ((mov_int_to_movwt
                                                           hi_32 IR11 mOVT_OP) :: l))
          | None -> None)
  | DIV ->
    if Int.eq imm32 Int.zero
    then None
    else let ins_lo =
           encode_arm32 (int_of_breg dst) uDIV_LO_OP 0 (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))
         in
         let ins_hi0 =
           encode_arm32 (int_of_breg dst) uDIV_HI_OP (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ 0)))))))) (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ 0))))
         in
         let ins_hi =
           encode_arm32 (int_of_ireg IR11) ins_hi0 0 (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))
         in
         let ins32 =
           encode_arm32 ins_hi ins_lo (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ 0))))))))))))))))
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ 0))))))))))))))))
         in
         let lo_32 =
           decode_arm32 imm32 0 (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ 0))))))))))))))))
         in
         let hi_32 =
           decode_arm32 imm32 (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ 0))))))))))))))))
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ 0))))))))))))))))
         in
         if Int.eq lo_32 imm32
         then Some ((mov_int_to_movwt lo_32 IR11 mOVW_OP) :: (ins32 :: []))
         else Some
                ((mov_int_to_movwt lo_32 IR11 mOVW_OP) :: ((mov_int_to_movwt
                                                             hi_32 IR11
                                                             mOVT_OP) :: (ins32 :: [])))
  | OR -> bpf_alu32_to_thumb_imm_comm oRR_I_OP OR dst imm32
  | AND -> bpf_alu32_to_thumb_imm_comm aND_I_OP AND dst imm32
  | LSH -> bpf_alu32_to_thumb_imm_shift_comm lSL_R_OP dst imm32
  | RSH -> bpf_alu32_to_thumb_imm_shift_comm lSR_R_OP dst imm32
  | NEG ->
    let ins_lo =
      encode_arm32 (int_of_ireg IR11) rSB_I_OP 0 (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))
    in
    let ins_hi =
      encode_arm32 (int_of_breg dst) Int.zero (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))))))
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        0))))
    in
    let ins32 =
      encode_arm32 ins_hi ins_lo (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ 0)))))))))))))))) (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))))))))))))))
    in
    let lo_32 =
      decode_arm32 imm32 0 (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ 0))))))))))))))))
    in
    let hi_32 =
      decode_arm32 imm32 (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ 0)))))))))))))))) (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ 0))))))))))))))))
    in
    if Int.eq lo_32 imm32
    then Some ((mov_int_to_movwt lo_32 IR11 mOVW_OP) :: (ins32 :: []))
    else Some
           ((mov_int_to_movwt lo_32 IR11 mOVW_OP) :: ((mov_int_to_movwt hi_32
                                                        IR11 mOVT_OP) :: (ins32 :: [])))
  | MOD -> None
  | XOR -> bpf_alu32_to_thumb_imm_comm eOR_I_OP XOR dst imm32
  | MOV ->
    let lo_32 =
      decode_arm32 imm32 0 (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ 0))))))))))))))))
    in
    let hi_32 =
      decode_arm32 imm32 (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ 0)))))))))))))))) (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ 0))))))))))))))))
    in
    if Int.eq lo_32 imm32
    then Some ((mov_int_to_movwt lo_32 (ireg_of_breg dst) mOVW_OP) :: [])
    else Some
           ((mov_int_to_movwt lo_32 (ireg_of_breg dst) mOVW_OP) :: ((mov_int_to_movwt
                                                                    hi_32
                                                                    (ireg_of_breg
                                                                    dst)
                                                                    mOVT_OP) :: []))
  | ARSH -> bpf_alu32_to_thumb_imm_shift_comm aSR_R_OP dst imm32

(** val jit_one :
    aluOp -> breg -> (breg, imm) sum -> listset -> listset ->
    ((bin_code * listset) * listset) option **)

let jit_one op dst src ld_set st_set =
  match src with
  | Inl r ->
    let (p, st_set1) = jit_call_save_reg dst r ld_set st_set in
    let (l1, ld_set1) = p in
    (match bpf_alu32_to_thumb_reg op dst (ireg_of_breg r) with
     | Some l2 -> Some (((app l1 l2), ld_set1), st_set1)
     | None -> None)
  | Inr i ->
    let (p, st_set1) = jit_call_save_imm dst ld_set st_set in
    let (l1, ld_set1) = p in
    (match bpf_alu32_to_thumb_imm op dst i with
     | Some l2 -> Some (((app l1 l2), ld_set1), st_set1)
     | None -> None)

(** val jit_sequence :
    bpf_code -> listset -> listset -> ((bin_code * listset) * listset) option **)

let rec jit_sequence l ld_set st_set =
  match l with
  | [] -> Some (([], ld_set), st_set)
  | hd :: tl ->
    (match hd with
     | Palu32 (op, dst, src) ->
       (match jit_one op dst src ld_set st_set with
        | Some p ->
          let (p0, st1) = p in
          let (l1, ld1) = p0 in
          (match jit_sequence tl ld1 st1 with
           | Some p1 ->
             let (p2, st2) = p1 in
             let (l2, ld2) = p2 in Some (((app l1 l2), ld2), st2)
           | None -> None)
        | None -> None)
     | _ -> None)

(** val jit_alu32_thumb_pc_add : int -> bin_code option **)

let jit_alu32_thumb_pc_add imm32 =
  if (&&) (Int.cmpu Cle Int.zero imm32)
       (Int.cmpu Cle imm32
         (Int.repr ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
           ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
           1)))))))))
  then let ins_lo =
         encode_arm32
           (Int.repr ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))
           aDD_I_OP 0 (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ 0))))
       in
       let ins_hi =
         encode_arm32
           (Int.repr ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))
           imm32 (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ 0)))))))) (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))
       in
       let ins32 =
         encode_arm32 ins_hi ins_lo (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ 0))))))))))))))))
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ (Stdlib.succ (Stdlib.succ
           (Stdlib.succ 0))))))))))))))))
       in
       Some (ins32 :: [])
  else None

(** val jit_alu32_thumb_pc : int -> bin_code option **)

let jit_alu32_thumb_pc num =
  match jit_alu32_thumb_pc_add (Int.repr (Z.of_nat num)) with
  | Some l ->
    let l_ldr =
      jit_alu32_thumb_mem_template_jit lDR_I_OP
        (Int.repr ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))
        (int_of_ireg IR12)
        (Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->2*p) 1))))))
    in
    let l_str =
      jit_alu32_thumb_mem_template_jit sTR_I_OP
        (Int.repr ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))
        (int_of_ireg IR12)
        (Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->2*p) 1))))))
    in
    Some (app (l_ldr :: []) (app l (l_str :: [])))
  | None -> None

(** val jit_alu32_thumb_store : listset -> bin_code **)

let rec jit_alu32_thumb_store = function
| [] -> []
| hd :: tl ->
  let l_str =
    jit_alu32_thumb_mem_template_jit sTR_I_OP (int_of_breg hd)
      (int_of_ireg IR12)
      (Int.mul (int_of_breg hd) (Int.repr ((fun p->2*p) ((fun p->2*p) 1))))
  in
  app (l_str :: []) (jit_alu32_thumb_store tl)

(** val jit_alu32_thumb_reset1 : listset -> bin_code **)

let rec jit_alu32_thumb_reset1 = function
| [] -> []
| hd :: tl ->
  app
    (if (&&) (Int.ltu (Int.repr ((fun p->1+2*p) 1)) (int_of_breg hd))
          (Int.ltu (int_of_breg hd)
            (Int.repr ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))
     then let l_ldr =
            jit_alu32_thumb_mem_template_jit lDR_I_OP (int_of_breg hd)
              (int_of_ireg IR13)
              (Int.mul (int_of_breg hd)
                (Int.repr ((fun p->2*p) ((fun p->2*p) 1))))
          in
          l_ldr :: []
     else []) (jit_alu32_thumb_reset1 tl)

(** val jit_alu32_thumb_reset : listset -> bin_code **)

let jit_alu32_thumb_reset ld_set =
  let l_ldr =
    jit_alu32_thumb_mem_template_jit lDR_I_OP
      (Int.repr ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))
      (int_of_ireg IR13)
      (Int.repr ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
        ((fun p->2*p) 1))))))
  in
  app (l_ldr :: []) (jit_alu32_thumb_reset1 ld_set)

(** val jit_alu32_post : bin_code **)

let jit_alu32_post =
  let l_ldr =
    jit_alu32_thumb_mem_template_jit lDR_I_OP (int_of_ireg IR13)
      (int_of_ireg IR13) Int.zero
  in
  let ins_rm =
    encode_arm32 (int_of_ireg IR14) bX_OP (Stdlib.succ (Stdlib.succ
      (Stdlib.succ 0))) (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ 0))))
  in
  let ins32 =
    encode_arm32 ins_rm nOP_OP (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ 0)))))))))))))))) (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))))))))))))))
  in
  app (l_ldr :: []) (ins32 :: [])

(** val jit_alu32_aux : bpf_code -> bin_code option **)

let jit_alu32_aux l =
  match jit_sequence l [] [] with
  | Some p ->
    let (p0, st_set) = p in
    let (cl, ld_set) = p0 in
    (match cl with
     | [] -> None
     | _ :: _ ->
       (match jit_alu32_thumb_pc (length l) with
        | Some l_pc ->
          Some
            (app cl
              (app l_pc
                (app (jit_alu32_thumb_store (sort_listset st_set))
                  (jit_alu32_thumb_reset (sort_listset ld_set)))))
        | None -> None))
  | None -> None

(** val jit_alu32 : bpf_code -> bin_code option **)

let jit_alu32 l =
  match jit_alu32_aux l with
  | Some bl -> Some (app jit_alu32_pre (app bl jit_alu32_post))
  | None -> None

(** val combiner_aux :
    (int * bpf_code) list -> int -> (int * (int * bin_code)) list option **)

let rec combiner_aux kl base =
  match kl with
  | [] -> Some []
  | p :: tl ->
    let (ep, l) = p in let _ = print_endline ("ep=  " ^ (Printf.sprintf "0x%02x" ep) ) in
    (match jit_alu32 l with
     | Some bl ->
       (match combiner_aux tl (add base (length bl)) with
        | Some cl -> Some ((ep, (base, bl)) :: cl)
        | None -> None)
     | None -> None)

(** val combiner :
    (int * bpf_code) list -> (int * (int * bin_code)) list option **)

let combiner kl =
  combiner_aux kl 0

(** val concat_bin :
    (int * (int * bin_code)) list -> (int * int) list * bin_code **)

let rec concat_bin = function
| [] -> ([], [])
| p :: tl ->
  let (ep, p0) = p in
  let (ofs, bl) = p0 in
  (((ep, ofs) :: (fst (concat_bin tl))), (app bl (snd (concat_bin tl))))

(** val whole_compiler : code -> ((int * int) list * bin_code) option **)

let whole_compiler c =
  match analyzer c with
  | Some kl ->
    (match kl with
     | [] -> Some ([], [])
     | _ :: _ ->
       (match combiner kl with
        | Some bl -> Some (concat_bin bl)
        | None -> None))
  | None -> None

(** val test_bitswap_int64 : int list **)

let test_bitswap_int64 =
  (Int64.repr ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    1))))))))))))))))) :: ((Int64.repr ((fun p->2*p) ((fun p->2*p)
                             ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
                             ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
                             ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
                             ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
                             ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
                             ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
                             ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
                             ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
                             ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
                             ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
                             1))))))))))))))))))))))))))))))))) :: ((Int64.repr
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))))))))))))))))))))))))))))) :: (
    (Int64.repr ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->1+2*p) 1)))))))))))))) :: ((Int64.repr ((fun p->1+2*p)
                                            ((fun p->2*p) ((fun p->2*p)
                                            ((fun p->2*p) ((fun p->1+2*p)
                                            ((fun p->1+2*p) ((fun p->1+2*p)
                                            ((fun p->2*p) ((fun p->1+2*p)
                                            ((fun p->2*p) ((fun p->1+2*p)
                                            ((fun p->2*p) ((fun p->1+2*p)
                                            ((fun p->2*p) ((fun p->2*p)
                                            ((fun p->2*p) ((fun p->2*p)
                                            1)))))))))))))))))) :: ((Int64.repr
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))))))))))) :: (
    (Int64.repr ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
      ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->2*p) 1)))))))))))))) :: ((Int64.repr ((fun p->2*p)
                                          ((fun p->2*p) ((fun p->1+2*p)
                                          ((fun p->1+2*p) ((fun p->2*p)
                                          ((fun p->2*p) ((fun p->1+2*p)
                                          ((fun p->2*p) ((fun p->2*p)
                                          ((fun p->1+2*p) ((fun p->1+2*p)
                                          ((fun p->2*p) ((fun p->2*p)
                                          ((fun p->2*p) 1))))))))))))))) :: (
    (Int64.repr ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
      ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: (
    (Int64.repr ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))))))))) :: (
    (Int64.repr ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))))))))) :: (
    (Int64.repr ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->1+2*p) 1))))))))))))))) :: ((Int64.repr ((fun p->2*p)
                                             ((fun p->2*p) ((fun p->1+2*p)
                                             ((fun p->1+2*p) ((fun p->1+2*p)
                                             ((fun p->2*p) ((fun p->1+2*p)
                                             ((fun p->2*p) ((fun p->2*p)
                                             ((fun p->2*p) ((fun p->1+2*p)
                                             ((fun p->2*p) 1))))))))))))) :: (
    (Int64.repr ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->1+2*p) 1)))))))))))))) :: ((Int64.repr ((fun p->2*p)
                                            ((fun p->2*p) ((fun p->1+2*p)
                                            ((fun p->1+2*p) ((fun p->2*p)
                                            ((fun p->1+2*p) ((fun p->1+2*p)
                                            ((fun p->2*p) ((fun p->2*p)
                                            ((fun p->2*p) ((fun p->1+2*p)
                                            ((fun p->2*p) ((fun p->1+2*p)
                                            ((fun p->2*p) 1))))))))))))))) :: (
    (Int64.repr ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      1))))))))))))))) :: ((Int64.repr ((fun p->2*p) ((fun p->2*p)
                             ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
                             ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
                             ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
                             ((fun p->2*p) 1))))))))))))) :: ((Int64.repr
                                                                ((fun p->2*p)
                                                                ((fun p->2*p)
                                                                ((fun p->1+2*p)
                                                                ((fun p->1+2*p)
                                                                ((fun p->1+2*p)
                                                                ((fun p->1+2*p)
                                                                ((fun p->1+2*p)
                                                                ((fun p->2*p)
                                                                ((fun p->2*p)
                                                                ((fun p->1+2*p)
                                                                ((fun p->2*p)
                                                                ((fun p->2*p)
                                                                ((fun p->1+2*p)
                                                                ((fun p->2*p)
                                                                1))))))))))))))) :: (
    (Int64.repr ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->1+2*p) 1)))))))))))))) :: ((Int64.repr ((fun p->2*p)
                                            ((fun p->2*p) ((fun p->1+2*p)
                                            ((fun p->1+2*p) ((fun p->2*p)
                                            ((fun p->2*p) ((fun p->1+2*p)
                                            ((fun p->2*p) ((fun p->2*p)
                                            ((fun p->2*p) ((fun p->2*p)
                                            ((fun p->2*p) ((fun p->2*p)
                                            1)))))))))))))) :: ((Int64.repr
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->1+2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->1+2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->1+2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->2*p)
                                                                  ((fun p->1+2*p)
                                                                  ((fun p->1+2*p)
                                                                  ((fun p->1+2*p)
                                                                  ((fun p->1+2*p)
                                                                  ((fun p->1+2*p)
                                                                  ((fun p->1+2*p)
                                                                  ((fun p->1+2*p)
                                                                  1)))))))))))))))))))))))))))))))))))))))) :: (
    (Int64.repr ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))) :: [])))))))))))))))))))))

(** val bitswap_ibpf_main : ((int * int) list * bin_code) option **)

let bitswap_ibpf_main =
  whole_compiler test_bitswap_int64
