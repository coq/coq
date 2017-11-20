
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)
 let rec add n0 m =
   match n0 with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val size_nat : positive -> nat **)

  let rec size_nat = function
  | XI p2 -> S (size_nat p2)
  | XO p2 -> S (size_nat p2)
  | XH -> S O

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val gcdn : nat -> positive -> positive -> positive **)

  let rec gcdn n0 a b =
    match n0 with
    | O -> XH
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> a
             | Lt -> gcdn n1 (sub b' a') a
             | Gt -> gcdn n1 (sub a' b') b)
          | XO b0 -> gcdn n1 a b0
          | XH -> XH)
       | XO a0 ->
         (match b with
          | XI _ -> gcdn n1 a0 b
          | XO b0 -> XO (gcdn n1 a0 b0)
          | XH -> XH)
       | XH -> XH)

  (** val gcd : positive -> positive -> positive **)

  let gcd a b =
    gcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module N =
 struct
  (** val of_nat : nat -> n **)

  let of_nat = function
  | O -> N0
  | S n' -> Npos (Coq_Pos.of_succ_nat n')
 end

(** val pow_pos : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

let rec pow_pos rmul x = function
| XI i0 -> let p = pow_pos rmul x i0 in rmul x (rmul p p)
| XO i0 -> let p = pow_pos rmul x i0 in rmul p p
| XH -> x

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n0 l default =
  match n0 with
  | O -> (match l with
          | [] -> default
          | x::_ -> x)
  | S m -> (match l with
            | [] -> default
            | _::t0 -> nth m t0 default)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::t0 -> (f a)::(map f t0)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b::t0 -> f b (fold_right f a0 t0)

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Coq_Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n0 =
    add m (opp n0)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val gtb : z -> z -> bool **)

  let gtb x y =
    match compare x y with
    | Gt -> true
    | _ -> false

  (** val max : z -> z -> z **)

  let max n0 m =
    match compare n0 m with
    | Lt -> m
    | _ -> n0

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val to_N : z -> n **)

  let to_N = function
  | Zpos p -> Npos p
  | _ -> N0

  (** val pos_div_eucl : positive -> z -> z * z **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let q0,r = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then (mul (Zpos (XO XH)) q0),r'
      else (add (mul (Zpos (XO XH)) q0) (Zpos XH)),(sub r' b)
    | XO a' ->
      let q0,r = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then (mul (Zpos (XO XH)) q0),r'
      else (add (mul (Zpos (XO XH)) q0) (Zpos XH)),(sub r' b)
    | XH -> if leb (Zpos (XO XH)) b then Z0,(Zpos XH) else (Zpos XH),Z0

  (** val div_eucl : z -> z -> z * z **)

  let div_eucl a b =
    match a with
    | Z0 -> Z0,Z0
    | Zpos a' ->
      (match b with
       | Z0 -> Z0,Z0
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let q0,r = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> (opp q0),Z0
          | _ -> (opp (add q0 (Zpos XH))),(add b r)))
    | Zneg a' ->
      (match b with
       | Z0 -> Z0,Z0
       | Zpos _ ->
         let q0,r = pos_div_eucl a' b in
         (match r with
          | Z0 -> (opp q0),Z0
          | _ -> (opp (add q0 (Zpos XH))),(sub b r))
       | Zneg b' -> let q0,r = pos_div_eucl a' (Zpos b') in q0,(opp r))

  (** val div : z -> z -> z **)

  let div a b =
    let q0,_ = div_eucl a b in q0

  (** val gcd : z -> z -> z **)

  let gcd a b =
    match a with
    | Z0 -> abs b
    | Zpos a0 ->
      (match b with
       | Z0 -> abs a
       | Zpos b0 -> Zpos (Coq_Pos.gcd a0 b0)
       | Zneg b0 -> Zpos (Coq_Pos.gcd a0 b0))
    | Zneg a0 ->
      (match b with
       | Z0 -> abs a
       | Zpos b0 -> Zpos (Coq_Pos.gcd a0 b0)
       | Zneg b0 -> Zpos (Coq_Pos.gcd a0 b0))
 end

(** val zeq_bool : z -> z -> bool **)

let zeq_bool x y =
  match Z.compare x y with
  | Eq -> true
  | _ -> false

type 'c pol =
| Pc of 'c
| Pinj of positive * 'c pol
| PX of 'c pol * positive * 'c pol

(** val p0 : 'a1 -> 'a1 pol **)

let p0 cO =
  Pc cO

(** val p1 : 'a1 -> 'a1 pol **)

let p1 cI =
  Pc cI

(** val peq : ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> bool **)

let rec peq ceqb p p' =
  match p with
  | Pc c -> (match p' with
             | Pc c' -> ceqb c c'
             | _ -> false)
  | Pinj (j, q0) ->
    (match p' with
     | Pinj (j', q') ->
       (match Coq_Pos.compare j j' with
        | Eq -> peq ceqb q0 q'
        | _ -> false)
     | _ -> false)
  | PX (p2, i, q0) ->
    (match p' with
     | PX (p'0, i', q') ->
       (match Coq_Pos.compare i i' with
        | Eq -> if peq ceqb p2 p'0 then peq ceqb q0 q' else false
        | _ -> false)
     | _ -> false)

(** val mkPinj : positive -> 'a1 pol -> 'a1 pol **)

let mkPinj j p = match p with
| Pc _ -> p
| Pinj (j', q0) -> Pinj ((Coq_Pos.add j j'), q0)
| PX (_, _, _) -> Pinj (j, p)

(** val mkPinj_pred : positive -> 'a1 pol -> 'a1 pol **)

let mkPinj_pred j p =
  match j with
  | XI j0 -> Pinj ((XO j0), p)
  | XO j0 -> Pinj ((Coq_Pos.pred_double j0), p)
  | XH -> p

(** val mkPX :
    'a1 -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol **)

let mkPX cO ceqb p i q0 =
  match p with
  | Pc c -> if ceqb c cO then mkPinj XH q0 else PX (p, i, q0)
  | Pinj (_, _) -> PX (p, i, q0)
  | PX (p', i', q') ->
    if peq ceqb q' (p0 cO)
    then PX (p', (Coq_Pos.add i' i), q0)
    else PX (p, i, q0)

(** val mkXi : 'a1 -> 'a1 -> positive -> 'a1 pol **)

let mkXi cO cI i =
  PX ((p1 cI), i, (p0 cO))

(** val mkX : 'a1 -> 'a1 -> 'a1 pol **)

let mkX cO cI =
  mkXi cO cI XH

(** val popp : ('a1 -> 'a1) -> 'a1 pol -> 'a1 pol **)

let rec popp copp = function
| Pc c -> Pc (copp c)
| Pinj (j, q0) -> Pinj (j, (popp copp q0))
| PX (p2, i, q0) -> PX ((popp copp p2), i, (popp copp q0))

(** val paddC : ('a1 -> 'a1 -> 'a1) -> 'a1 pol -> 'a1 -> 'a1 pol **)

let rec paddC cadd p c =
  match p with
  | Pc c1 -> Pc (cadd c1 c)
  | Pinj (j, q0) -> Pinj (j, (paddC cadd q0 c))
  | PX (p2, i, q0) -> PX (p2, i, (paddC cadd q0 c))

(** val psubC : ('a1 -> 'a1 -> 'a1) -> 'a1 pol -> 'a1 -> 'a1 pol **)

let rec psubC csub p c =
  match p with
  | Pc c1 -> Pc (csub c1 c)
  | Pinj (j, q0) -> Pinj (j, (psubC csub q0 c))
  | PX (p2, i, q0) -> PX (p2, i, (psubC csub q0 c))

(** val paddI :
    ('a1 -> 'a1 -> 'a1) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol ->
    positive -> 'a1 pol -> 'a1 pol **)

let rec paddI cadd pop q0 j = function
| Pc c -> mkPinj j (paddC cadd q0 c)
| Pinj (j', q') ->
  (match Z.pos_sub j' j with
   | Z0 -> mkPinj j (pop q' q0)
   | Zpos k -> mkPinj j (pop (Pinj (k, q')) q0)
   | Zneg k -> mkPinj j' (paddI cadd pop q0 k q'))
| PX (p2, i, q') ->
  (match j with
   | XI j0 -> PX (p2, i, (paddI cadd pop q0 (XO j0) q'))
   | XO j0 -> PX (p2, i, (paddI cadd pop q0 (Coq_Pos.pred_double j0) q'))
   | XH -> PX (p2, i, (pop q' q0)))

(** val psubI :
    ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 pol -> 'a1 pol -> 'a1 pol) ->
    'a1 pol -> positive -> 'a1 pol -> 'a1 pol **)

let rec psubI cadd copp pop q0 j = function
| Pc c -> mkPinj j (paddC cadd (popp copp q0) c)
| Pinj (j', q') ->
  (match Z.pos_sub j' j with
   | Z0 -> mkPinj j (pop q' q0)
   | Zpos k -> mkPinj j (pop (Pinj (k, q')) q0)
   | Zneg k -> mkPinj j' (psubI cadd copp pop q0 k q'))
| PX (p2, i, q') ->
  (match j with
   | XI j0 -> PX (p2, i, (psubI cadd copp pop q0 (XO j0) q'))
   | XO j0 -> PX (p2, i, (psubI cadd copp pop q0 (Coq_Pos.pred_double j0) q'))
   | XH -> PX (p2, i, (pop q' q0)))

(** val paddX :
    'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol
    -> positive -> 'a1 pol -> 'a1 pol **)

let rec paddX cO ceqb pop p' i' p = match p with
| Pc _ -> PX (p', i', p)
| Pinj (j, q') ->
  (match j with
   | XI j0 -> PX (p', i', (Pinj ((XO j0), q')))
   | XO j0 -> PX (p', i', (Pinj ((Coq_Pos.pred_double j0), q')))
   | XH -> PX (p', i', q'))
| PX (p2, i, q') ->
  (match Z.pos_sub i i' with
   | Z0 -> mkPX cO ceqb (pop p2 p') i q'
   | Zpos k -> mkPX cO ceqb (pop (PX (p2, k, (p0 cO))) p') i' q'
   | Zneg k -> mkPX cO ceqb (paddX cO ceqb pop p' k p2) i q')

(** val psubX :
    'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol -> 'a1
    pol) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol **)

let rec psubX cO copp ceqb pop p' i' p = match p with
| Pc _ -> PX ((popp copp p'), i', p)
| Pinj (j, q') ->
  (match j with
   | XI j0 -> PX ((popp copp p'), i', (Pinj ((XO j0), q')))
   | XO j0 -> PX ((popp copp p'), i', (Pinj ((Coq_Pos.pred_double j0), q')))
   | XH -> PX ((popp copp p'), i', q'))
| PX (p2, i, q') ->
  (match Z.pos_sub i i' with
   | Z0 -> mkPX cO ceqb (pop p2 p') i q'
   | Zpos k -> mkPX cO ceqb (pop (PX (p2, k, (p0 cO))) p') i' q'
   | Zneg k -> mkPX cO ceqb (psubX cO copp ceqb pop p' k p2) i q')

(** val padd :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol
    -> 'a1 pol **)

let rec padd cO cadd ceqb p = function
| Pc c' -> paddC cadd p c'
| Pinj (j', q') -> paddI cadd (padd cO cadd ceqb) q' j' p
| PX (p'0, i', q') ->
  (match p with
   | Pc c -> PX (p'0, i', (paddC cadd q' c))
   | Pinj (j, q0) ->
     (match j with
      | XI j0 -> PX (p'0, i', (padd cO cadd ceqb (Pinj ((XO j0), q0)) q'))
      | XO j0 ->
        PX (p'0, i',
          (padd cO cadd ceqb (Pinj ((Coq_Pos.pred_double j0), q0)) q'))
      | XH -> PX (p'0, i', (padd cO cadd ceqb q0 q')))
   | PX (p2, i, q0) ->
     (match Z.pos_sub i i' with
      | Z0 ->
        mkPX cO ceqb (padd cO cadd ceqb p2 p'0) i (padd cO cadd ceqb q0 q')
      | Zpos k ->
        mkPX cO ceqb (padd cO cadd ceqb (PX (p2, k, (p0 cO))) p'0) i'
          (padd cO cadd ceqb q0 q')
      | Zneg k ->
        mkPX cO ceqb (paddX cO ceqb (padd cO cadd ceqb) p'0 k p2) i
          (padd cO cadd ceqb q0 q')))

(** val psub :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1
    -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol **)

let rec psub cO cadd csub copp ceqb p = function
| Pc c' -> psubC csub p c'
| Pinj (j', q') -> psubI cadd copp (psub cO cadd csub copp ceqb) q' j' p
| PX (p'0, i', q') ->
  (match p with
   | Pc c -> PX ((popp copp p'0), i', (paddC cadd (popp copp q') c))
   | Pinj (j, q0) ->
     (match j with
      | XI j0 ->
        PX ((popp copp p'0), i',
          (psub cO cadd csub copp ceqb (Pinj ((XO j0), q0)) q'))
      | XO j0 ->
        PX ((popp copp p'0), i',
          (psub cO cadd csub copp ceqb (Pinj ((Coq_Pos.pred_double j0), q0))
            q'))
      | XH -> PX ((popp copp p'0), i', (psub cO cadd csub copp ceqb q0 q')))
   | PX (p2, i, q0) ->
     (match Z.pos_sub i i' with
      | Z0 ->
        mkPX cO ceqb (psub cO cadd csub copp ceqb p2 p'0) i
          (psub cO cadd csub copp ceqb q0 q')
      | Zpos k ->
        mkPX cO ceqb (psub cO cadd csub copp ceqb (PX (p2, k, (p0 cO))) p'0)
          i' (psub cO cadd csub copp ceqb q0 q')
      | Zneg k ->
        mkPX cO ceqb
          (psubX cO copp ceqb (psub cO cadd csub copp ceqb) p'0 k p2) i
          (psub cO cadd csub copp ceqb q0 q')))

(** val pmulC_aux :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 ->
    'a1 pol **)

let rec pmulC_aux cO cmul ceqb p c =
  match p with
  | Pc c' -> Pc (cmul c' c)
  | Pinj (j, q0) -> mkPinj j (pmulC_aux cO cmul ceqb q0 c)
  | PX (p2, i, q0) ->
    mkPX cO ceqb (pmulC_aux cO cmul ceqb p2 c) i (pmulC_aux cO cmul ceqb q0 c)

(** val pmulC :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol ->
    'a1 -> 'a1 pol **)

let pmulC cO cI cmul ceqb p c =
  if ceqb c cO
  then p0 cO
  else if ceqb c cI then p else pmulC_aux cO cmul ceqb p c

(** val pmulI :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 pol ->
    'a1 pol -> 'a1 pol) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol **)

let rec pmulI cO cI cmul ceqb pmul0 q0 j = function
| Pc c -> mkPinj j (pmulC cO cI cmul ceqb q0 c)
| Pinj (j', q') ->
  (match Z.pos_sub j' j with
   | Z0 -> mkPinj j (pmul0 q' q0)
   | Zpos k -> mkPinj j (pmul0 (Pinj (k, q')) q0)
   | Zneg k -> mkPinj j' (pmulI cO cI cmul ceqb pmul0 q0 k q'))
| PX (p', i', q') ->
  (match j with
   | XI j' ->
     mkPX cO ceqb (pmulI cO cI cmul ceqb pmul0 q0 j p') i'
       (pmulI cO cI cmul ceqb pmul0 q0 (XO j') q')
   | XO j' ->
     mkPX cO ceqb (pmulI cO cI cmul ceqb pmul0 q0 j p') i'
       (pmulI cO cI cmul ceqb pmul0 q0 (Coq_Pos.pred_double j') q')
   | XH ->
     mkPX cO ceqb (pmulI cO cI cmul ceqb pmul0 q0 XH p') i' (pmul0 q' q0))

(** val pmul :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol **)

let rec pmul cO cI cadd cmul ceqb p p'' = match p'' with
| Pc c -> pmulC cO cI cmul ceqb p c
| Pinj (j', q') -> pmulI cO cI cmul ceqb (pmul cO cI cadd cmul ceqb) q' j' p
| PX (p', i', q') ->
  (match p with
   | Pc c -> pmulC cO cI cmul ceqb p'' c
   | Pinj (j, q0) ->
     let qQ' =
       match j with
       | XI j0 -> pmul cO cI cadd cmul ceqb (Pinj ((XO j0), q0)) q'
       | XO j0 ->
         pmul cO cI cadd cmul ceqb (Pinj ((Coq_Pos.pred_double j0), q0)) q'
       | XH -> pmul cO cI cadd cmul ceqb q0 q'
     in
     mkPX cO ceqb (pmul cO cI cadd cmul ceqb p p') i' qQ'
   | PX (p2, i, q0) ->
     let qQ' = pmul cO cI cadd cmul ceqb q0 q' in
     let pQ' = pmulI cO cI cmul ceqb (pmul cO cI cadd cmul ceqb) q' XH p2 in
     let qP' = pmul cO cI cadd cmul ceqb (mkPinj XH q0) p' in
     let pP' = pmul cO cI cadd cmul ceqb p2 p' in
     padd cO cadd ceqb
       (mkPX cO ceqb (padd cO cadd ceqb (mkPX cO ceqb pP' i (p0 cO)) qP') i'
         (p0 cO)) (mkPX cO ceqb pQ' i qQ'))

(** val psquare :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> 'a1 pol -> 'a1 pol **)

let rec psquare cO cI cadd cmul ceqb = function
| Pc c -> Pc (cmul c c)
| Pinj (j, q0) -> Pinj (j, (psquare cO cI cadd cmul ceqb q0))
| PX (p2, i, q0) ->
  let twoPQ =
    pmul cO cI cadd cmul ceqb p2
      (mkPinj XH (pmulC cO cI cmul ceqb q0 (cadd cI cI)))
  in
  let q2 = psquare cO cI cadd cmul ceqb q0 in
  let p3 = psquare cO cI cadd cmul ceqb p2 in
  mkPX cO ceqb (padd cO cadd ceqb (mkPX cO ceqb p3 i (p0 cO)) twoPQ) i q2

type 'c pExpr =
| PEc of 'c
| PEX of positive
| PEadd of 'c pExpr * 'c pExpr
| PEsub of 'c pExpr * 'c pExpr
| PEmul of 'c pExpr * 'c pExpr
| PEopp of 'c pExpr
| PEpow of 'c pExpr * n

(** val mk_X : 'a1 -> 'a1 -> positive -> 'a1 pol **)

let mk_X cO cI j =
  mkPinj_pred j (mkX cO cI)

(** val ppow_pos :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> ('a1 pol -> 'a1 pol) -> 'a1 pol -> 'a1 pol -> positive -> 'a1
    pol **)

let rec ppow_pos cO cI cadd cmul ceqb subst_l res p = function
| XI p3 ->
  subst_l
    (pmul cO cI cadd cmul ceqb
      (ppow_pos cO cI cadd cmul ceqb subst_l
        (ppow_pos cO cI cadd cmul ceqb subst_l res p p3) p p3) p)
| XO p3 ->
  ppow_pos cO cI cadd cmul ceqb subst_l
    (ppow_pos cO cI cadd cmul ceqb subst_l res p p3) p p3
| XH -> subst_l (pmul cO cI cadd cmul ceqb res p)

(** val ppow_N :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> ('a1 pol -> 'a1 pol) -> 'a1 pol -> n -> 'a1 pol **)

let ppow_N cO cI cadd cmul ceqb subst_l p = function
| N0 -> p1 cI
| Npos p2 -> ppow_pos cO cI cadd cmul ceqb subst_l (p1 cI) p p2

(** val norm_aux :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pExpr -> 'a1 pol **)

let rec norm_aux cO cI cadd cmul csub copp ceqb = function
| PEc c -> Pc c
| PEX j -> mk_X cO cI j
| PEadd (pe1, pe2) ->
  (match pe1 with
   | PEopp pe3 ->
     psub cO cadd csub copp ceqb
       (norm_aux cO cI cadd cmul csub copp ceqb pe2)
       (norm_aux cO cI cadd cmul csub copp ceqb pe3)
   | _ ->
     (match pe2 with
      | PEopp pe3 ->
        psub cO cadd csub copp ceqb
          (norm_aux cO cI cadd cmul csub copp ceqb pe1)
          (norm_aux cO cI cadd cmul csub copp ceqb pe3)
      | _ ->
        padd cO cadd ceqb (norm_aux cO cI cadd cmul csub copp ceqb pe1)
          (norm_aux cO cI cadd cmul csub copp ceqb pe2)))
| PEsub (pe1, pe2) ->
  psub cO cadd csub copp ceqb (norm_aux cO cI cadd cmul csub copp ceqb pe1)
    (norm_aux cO cI cadd cmul csub copp ceqb pe2)
| PEmul (pe1, pe2) ->
  pmul cO cI cadd cmul ceqb (norm_aux cO cI cadd cmul csub copp ceqb pe1)
    (norm_aux cO cI cadd cmul csub copp ceqb pe2)
| PEopp pe1 -> popp copp (norm_aux cO cI cadd cmul csub copp ceqb pe1)
| PEpow (pe1, n0) ->
  ppow_N cO cI cadd cmul ceqb (fun p -> p)
    (norm_aux cO cI cadd cmul csub copp ceqb pe1) n0

type 'a bFormula =
| TT
| FF
| X
| A of 'a
| Cj of 'a bFormula * 'a bFormula
| D of 'a bFormula * 'a bFormula
| N of 'a bFormula
| I of 'a bFormula * 'a bFormula

(** val map_bformula : ('a1 -> 'a2) -> 'a1 bFormula -> 'a2 bFormula **)

let rec map_bformula fct = function
| TT -> TT
| FF -> FF
| X -> X
| A a -> A (fct a)
| Cj (f1, f2) -> Cj ((map_bformula fct f1), (map_bformula fct f2))
| D (f1, f2) -> D ((map_bformula fct f1), (map_bformula fct f2))
| N f0 -> N (map_bformula fct f0)
| I (f1, f2) -> I ((map_bformula fct f1), (map_bformula fct f2))

type 'x clause = 'x list

type 'x cnf = 'x clause list

(** val tt : 'a1 cnf **)

let tt =
  []

(** val ff : 'a1 cnf **)

let ff =
  []::[]

(** val add_term :
    ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> 'a1 -> 'a1 clause -> 'a1
    clause option **)

let rec add_term unsat deduce t0 = function
| [] ->
  (match deduce t0 t0 with
   | Some u -> if unsat u then None else Some (t0::[])
   | None -> Some (t0::[]))
| t'::cl0 ->
  (match deduce t0 t' with
   | Some u ->
     if unsat u
     then None
     else (match add_term unsat deduce t0 cl0 with
           | Some cl' -> Some (t'::cl')
           | None -> None)
   | None ->
     (match add_term unsat deduce t0 cl0 with
      | Some cl' -> Some (t'::cl')
      | None -> None))

(** val or_clause :
    ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> 'a1 clause -> 'a1 clause
    -> 'a1 clause option **)

let rec or_clause unsat deduce cl1 cl2 =
  match cl1 with
  | [] -> Some cl2
  | t0::cl ->
    (match add_term unsat deduce t0 cl2 with
     | Some cl' -> or_clause unsat deduce cl cl'
     | None -> None)

(** val or_clause_cnf :
    ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> 'a1 clause -> 'a1 cnf ->
    'a1 cnf **)

let or_clause_cnf unsat deduce t0 f =
  fold_right (fun e acc ->
    match or_clause unsat deduce t0 e with
    | Some cl -> cl::acc
    | None -> acc) [] f

(** val or_cnf :
    ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> 'a1 cnf -> 'a1 cnf -> 'a1
    cnf **)

let rec or_cnf unsat deduce f f' =
  match f with
  | [] -> tt
  | e::rst ->
    app (or_cnf unsat deduce rst f') (or_clause_cnf unsat deduce e f')

(** val and_cnf : 'a1 cnf -> 'a1 cnf -> 'a1 cnf **)

let and_cnf =
  app

(** val xcnf :
    ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> ('a1 -> 'a2 cnf) -> ('a1
    -> 'a2 cnf) -> bool -> 'a1 bFormula -> 'a2 cnf **)

let rec xcnf unsat deduce normalise0 negate0 pol0 = function
| TT -> if pol0 then tt else ff
| FF -> if pol0 then ff else tt
| X -> ff
| A x -> if pol0 then normalise0 x else negate0 x
| Cj (e1, e2) ->
  if pol0
  then and_cnf (xcnf unsat deduce normalise0 negate0 pol0 e1)
         (xcnf unsat deduce normalise0 negate0 pol0 e2)
  else or_cnf unsat deduce (xcnf unsat deduce normalise0 negate0 pol0 e1)
         (xcnf unsat deduce normalise0 negate0 pol0 e2)
| D (e1, e2) ->
  if pol0
  then or_cnf unsat deduce (xcnf unsat deduce normalise0 negate0 pol0 e1)
         (xcnf unsat deduce normalise0 negate0 pol0 e2)
  else and_cnf (xcnf unsat deduce normalise0 negate0 pol0 e1)
         (xcnf unsat deduce normalise0 negate0 pol0 e2)
| N e -> xcnf unsat deduce normalise0 negate0 (negb pol0) e
| I (e1, e2) ->
  if pol0
  then or_cnf unsat deduce
         (xcnf unsat deduce normalise0 negate0 (negb pol0) e1)
         (xcnf unsat deduce normalise0 negate0 pol0 e2)
  else and_cnf (xcnf unsat deduce normalise0 negate0 (negb pol0) e1)
         (xcnf unsat deduce normalise0 negate0 pol0 e2)

(** val cnf_checker :
    ('a1 list -> 'a2 -> bool) -> 'a1 cnf -> 'a2 list -> bool **)

let rec cnf_checker checker f l =
  match f with
  | [] -> true
  | e::f0 ->
    (match l with
     | [] -> false
     | c::l0 -> if checker e c then cnf_checker checker f0 l0 else false)

(** val tauto_checker :
    ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> ('a1 -> 'a2 cnf) -> ('a1
    -> 'a2 cnf) -> ('a2 list -> 'a3 -> bool) -> 'a1 bFormula -> 'a3 list ->
    bool **)

let tauto_checker unsat deduce normalise0 negate0 checker f w =
  cnf_checker checker (xcnf unsat deduce normalise0 negate0 true f) w

(** val cneqb : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> bool **)

let cneqb ceqb x y =
  negb (ceqb x y)

(** val cltb :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> bool **)

let cltb ceqb cleb x y =
  (&&) (cleb x y) (cneqb ceqb x y)

type 'c polC = 'c pol

type op1 =
| Equal
| NonEqual
| Strict
| NonStrict

type 'c nFormula = 'c polC * op1

(** val opMult : op1 -> op1 -> op1 option **)

let opMult o o' =
  match o with
  | Equal -> Some Equal
  | NonEqual ->
    (match o' with
     | Equal -> Some Equal
     | NonEqual -> Some NonEqual
     | _ -> None)
  | Strict -> (match o' with
               | NonEqual -> None
               | _ -> Some o')
  | NonStrict ->
    (match o' with
     | Equal -> Some Equal
     | NonEqual -> None
     | _ -> Some NonStrict)

(** val opAdd : op1 -> op1 -> op1 option **)

let opAdd o o' =
  match o with
  | Equal -> Some o'
  | NonEqual -> (match o' with
                 | Equal -> Some NonEqual
                 | _ -> None)
  | Strict -> (match o' with
               | NonEqual -> None
               | _ -> Some Strict)
  | NonStrict ->
    (match o' with
     | Equal -> Some NonStrict
     | NonEqual -> None
     | x -> Some x)

type 'c psatz =
| PsatzIn of nat
| PsatzSquare of 'c polC
| PsatzMulC of 'c polC * 'c psatz
| PsatzMulE of 'c psatz * 'c psatz
| PsatzAdd of 'c psatz * 'c psatz
| PsatzC of 'c
| PsatzZ

(** val map_option : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option **)

let map_option f = function
| Some x -> f x
| None -> None

(** val map_option2 :
    ('a1 -> 'a2 -> 'a3 option) -> 'a1 option -> 'a2 option -> 'a3 option **)

let map_option2 f o o' =
  match o with
  | Some x -> (match o' with
               | Some x' -> f x x'
               | None -> None)
  | None -> None

(** val pexpr_times_nformula :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> 'a1 polC -> 'a1 nFormula -> 'a1 nFormula option **)

let pexpr_times_nformula cO cI cplus ctimes ceqb e = function
| ef,o ->
  (match o with
   | Equal -> Some ((pmul cO cI cplus ctimes ceqb e ef),Equal)
   | _ -> None)

(** val nformula_times_nformula :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> 'a1 nFormula -> 'a1 nFormula -> 'a1 nFormula option **)

let nformula_times_nformula cO cI cplus ctimes ceqb f1 f2 =
  let e1,o1 = f1 in
  let e2,o2 = f2 in
  map_option (fun x -> Some ((pmul cO cI cplus ctimes ceqb e1 e2),x))
    (opMult o1 o2)

(** val nformula_plus_nformula :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula -> 'a1
    nFormula -> 'a1 nFormula option **)

let nformula_plus_nformula cO cplus ceqb f1 f2 =
  let e1,o1 = f1 in
  let e2,o2 = f2 in
  map_option (fun x -> Some ((padd cO cplus ceqb e1 e2),x)) (opAdd o1 o2)

(** val eval_Psatz :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula list -> 'a1 psatz -> 'a1
    nFormula option **)

let rec eval_Psatz cO cI cplus ctimes ceqb cleb l = function
| PsatzIn n0 -> Some (nth n0 l ((Pc cO),Equal))
| PsatzSquare e0 -> Some ((psquare cO cI cplus ctimes ceqb e0),NonStrict)
| PsatzMulC (re, e0) ->
  map_option (pexpr_times_nformula cO cI cplus ctimes ceqb re)
    (eval_Psatz cO cI cplus ctimes ceqb cleb l e0)
| PsatzMulE (f1, f2) ->
  map_option2 (nformula_times_nformula cO cI cplus ctimes ceqb)
    (eval_Psatz cO cI cplus ctimes ceqb cleb l f1)
    (eval_Psatz cO cI cplus ctimes ceqb cleb l f2)
| PsatzAdd (f1, f2) ->
  map_option2 (nformula_plus_nformula cO cplus ceqb)
    (eval_Psatz cO cI cplus ctimes ceqb cleb l f1)
    (eval_Psatz cO cI cplus ctimes ceqb cleb l f2)
| PsatzC c -> if cltb ceqb cleb cO c then Some ((Pc c),Strict) else None
| PsatzZ -> Some ((Pc cO),Equal)

(** val check_inconsistent :
    'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula ->
    bool **)

let check_inconsistent cO ceqb cleb = function
| e,op ->
  (match e with
   | Pc c ->
     (match op with
      | Equal -> cneqb ceqb c cO
      | NonEqual -> ceqb c cO
      | Strict -> cleb c cO
      | NonStrict -> cltb ceqb cleb c cO)
   | _ -> false)

(** val check_normalised_formulas :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula list -> 'a1 psatz -> bool **)

let check_normalised_formulas cO cI cplus ctimes ceqb cleb l cm =
  match eval_Psatz cO cI cplus ctimes ceqb cleb l cm with
  | Some f -> check_inconsistent cO ceqb cleb f
  | None -> false

type op2 =
| OpEq
| OpNEq
| OpLe
| OpGe
| OpLt
| OpGt

type 't formula = { flhs : 't pExpr; fop : op2; frhs : 't pExpr }

(** val norm :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pExpr -> 'a1 pol **)

let norm =
  norm_aux

(** val psub0 :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1
    -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol **)

let psub0 =
  psub

(** val padd0 :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol
    -> 'a1 pol **)

let padd0 =
  padd

(** val xnormalise :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 formula -> 'a1
    nFormula list **)

let xnormalise cO cI cplus ctimes cminus copp ceqb t0 =
  let { flhs = lhs; fop = o; frhs = rhs } = t0 in
  let lhs0 = norm cO cI cplus ctimes cminus copp ceqb lhs in
  let rhs0 = norm cO cI cplus ctimes cminus copp ceqb rhs in
  (match o with
   | OpEq ->
     ((psub0 cO cplus cminus copp ceqb lhs0 rhs0),Strict)::(((psub0 cO cplus
                                                               cminus copp
                                                               ceqb rhs0 lhs0),Strict)::[])
   | OpNEq -> ((psub0 cO cplus cminus copp ceqb lhs0 rhs0),Equal)::[]
   | OpLe -> ((psub0 cO cplus cminus copp ceqb lhs0 rhs0),Strict)::[]
   | OpGe -> ((psub0 cO cplus cminus copp ceqb rhs0 lhs0),Strict)::[]
   | OpLt -> ((psub0 cO cplus cminus copp ceqb lhs0 rhs0),NonStrict)::[]
   | OpGt -> ((psub0 cO cplus cminus copp ceqb rhs0 lhs0),NonStrict)::[])

(** val cnf_normalise :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 formula -> 'a1
    nFormula cnf **)

let cnf_normalise cO cI cplus ctimes cminus copp ceqb t0 =
  map (fun x -> x::[]) (xnormalise cO cI cplus ctimes cminus copp ceqb t0)

(** val xnegate :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 formula -> 'a1
    nFormula list **)

let xnegate cO cI cplus ctimes cminus copp ceqb t0 =
  let { flhs = lhs; fop = o; frhs = rhs } = t0 in
  let lhs0 = norm cO cI cplus ctimes cminus copp ceqb lhs in
  let rhs0 = norm cO cI cplus ctimes cminus copp ceqb rhs in
  (match o with
   | OpEq -> ((psub0 cO cplus cminus copp ceqb lhs0 rhs0),Equal)::[]
   | OpNEq ->
     ((psub0 cO cplus cminus copp ceqb lhs0 rhs0),Strict)::(((psub0 cO cplus
                                                               cminus copp
                                                               ceqb rhs0 lhs0),Strict)::[])
   | OpLe -> ((psub0 cO cplus cminus copp ceqb rhs0 lhs0),NonStrict)::[]
   | OpGe -> ((psub0 cO cplus cminus copp ceqb lhs0 rhs0),NonStrict)::[]
   | OpLt -> ((psub0 cO cplus cminus copp ceqb rhs0 lhs0),Strict)::[]
   | OpGt -> ((psub0 cO cplus cminus copp ceqb lhs0 rhs0),Strict)::[])

(** val cnf_negate :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 formula -> 'a1
    nFormula cnf **)

let cnf_negate cO cI cplus ctimes cminus copp ceqb t0 =
  map (fun x -> x::[]) (xnegate cO cI cplus ctimes cminus copp ceqb t0)

(** val xdenorm : positive -> 'a1 pol -> 'a1 pExpr **)

let rec xdenorm jmp = function
| Pc c -> PEc c
| Pinj (j, p2) -> xdenorm (Coq_Pos.add j jmp) p2
| PX (p2, j, q0) ->
  PEadd ((PEmul ((xdenorm jmp p2), (PEpow ((PEX jmp), (Npos j))))),
    (xdenorm (Coq_Pos.succ jmp) q0))

(** val denorm : 'a1 pol -> 'a1 pExpr **)

let denorm p =
  xdenorm XH p

(** val map_PExpr : ('a2 -> 'a1) -> 'a2 pExpr -> 'a1 pExpr **)

let rec map_PExpr c_of_S = function
| PEc c -> PEc (c_of_S c)
| PEX p -> PEX p
| PEadd (e1, e2) -> PEadd ((map_PExpr c_of_S e1), (map_PExpr c_of_S e2))
| PEsub (e1, e2) -> PEsub ((map_PExpr c_of_S e1), (map_PExpr c_of_S e2))
| PEmul (e1, e2) -> PEmul ((map_PExpr c_of_S e1), (map_PExpr c_of_S e2))
| PEopp e0 -> PEopp (map_PExpr c_of_S e0)
| PEpow (e0, n0) -> PEpow ((map_PExpr c_of_S e0), n0)

(** val map_Formula : ('a2 -> 'a1) -> 'a2 formula -> 'a1 formula **)

let map_Formula c_of_S f =
  let { flhs = l; fop = o; frhs = r } = f in
  { flhs = (map_PExpr c_of_S l); fop = o; frhs = (map_PExpr c_of_S r) }

(** val simpl_cone :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 psatz ->
    'a1 psatz **)

let simpl_cone cO cI ctimes ceqb e = match e with
| PsatzSquare t0 ->
  (match t0 with
   | Pc c -> if ceqb cO c then PsatzZ else PsatzC (ctimes c c)
   | _ -> PsatzSquare t0)
| PsatzMulE (t1, t2) ->
  (match t1 with
   | PsatzMulE (x, x0) ->
     (match x with
      | PsatzC p2 ->
        (match t2 with
         | PsatzC c -> PsatzMulE ((PsatzC (ctimes c p2)), x0)
         | PsatzZ -> PsatzZ
         | _ -> e)
      | _ ->
        (match x0 with
         | PsatzC p2 ->
           (match t2 with
            | PsatzC c -> PsatzMulE ((PsatzC (ctimes c p2)), x)
            | PsatzZ -> PsatzZ
            | _ -> e)
         | _ ->
           (match t2 with
            | PsatzC c -> if ceqb cI c then t1 else PsatzMulE (t1, t2)
            | PsatzZ -> PsatzZ
            | _ -> e)))
   | PsatzC c ->
     (match t2 with
      | PsatzMulE (x, x0) ->
        (match x with
         | PsatzC p2 -> PsatzMulE ((PsatzC (ctimes c p2)), x0)
         | _ ->
           (match x0 with
            | PsatzC p2 -> PsatzMulE ((PsatzC (ctimes c p2)), x)
            | _ -> if ceqb cI c then t2 else PsatzMulE (t1, t2)))
      | PsatzAdd (y, z0) ->
        PsatzAdd ((PsatzMulE ((PsatzC c), y)), (PsatzMulE ((PsatzC c), z0)))
      | PsatzC c0 -> PsatzC (ctimes c c0)
      | PsatzZ -> PsatzZ
      | _ -> if ceqb cI c then t2 else PsatzMulE (t1, t2))
   | PsatzZ -> PsatzZ
   | _ ->
     (match t2 with
      | PsatzC c -> if ceqb cI c then t1 else PsatzMulE (t1, t2)
      | PsatzZ -> PsatzZ
      | _ -> e))
| PsatzAdd (t1, t2) ->
  (match t1 with
   | PsatzZ -> t2
   | _ -> (match t2 with
           | PsatzZ -> t1
           | _ -> PsatzAdd (t1, t2)))
| _ -> e

type q = { qnum : z; qden : positive }

(** val qnum : q -> z **)

let qnum x = x.qnum

(** val qden : q -> positive **)

let qden x = x.qden

(** val qeq_bool : q -> q -> bool **)

let qeq_bool x y =
  zeq_bool (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qle_bool : q -> q -> bool **)

let qle_bool x y =
  Z.leb (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden)));
    qden = (Coq_Pos.mul x.qden y.qden) }

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (Z.mul x.qnum y.qnum); qden = (Coq_Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

(** val qinv : q -> q **)

let qinv x =
  match x.qnum with
  | Z0 -> { qnum = Z0; qden = XH }
  | Zpos p -> { qnum = (Zpos x.qden); qden = p }
  | Zneg p -> { qnum = (Zneg x.qden); qden = p }

(** val qpower_positive : q -> positive -> q **)

let qpower_positive =
  pow_pos qmult

(** val qpower : q -> z -> q **)

let qpower q0 = function
| Z0 -> { qnum = (Zpos XH); qden = XH }
| Zpos p -> qpower_positive q0 p
| Zneg p -> qinv (qpower_positive q0 p)

type 'a t =
| Empty
| Leaf of 'a
| Node of 'a t * 'a * 'a t

(** val find : 'a1 -> 'a1 t -> positive -> 'a1 **)

let rec find default vm p =
  match vm with
  | Empty -> default
  | Leaf i -> i
  | Node (l, e, r) ->
    (match p with
     | XI p2 -> find default r p2
     | XO p2 -> find default l p2
     | XH -> e)

(** val singleton : 'a1 -> positive -> 'a1 -> 'a1 t **)

let rec singleton default x v =
  match x with
  | XI p -> Node (Empty, default, (singleton default p v))
  | XO p -> Node ((singleton default p v), default, Empty)
  | XH -> Leaf v

(** val vm_add : 'a1 -> positive -> 'a1 -> 'a1 t -> 'a1 t **)

let rec vm_add default x v = function
| Empty -> singleton default x v
| Leaf vl ->
  (match x with
   | XI p -> Node (Empty, vl, (singleton default p v))
   | XO p -> Node ((singleton default p v), vl, Empty)
   | XH -> Leaf v)
| Node (l, o, r) ->
  (match x with
   | XI p -> Node (l, o, (vm_add default p v r))
   | XO p -> Node ((vm_add default p v l), o, r)
   | XH -> Node (l, v, r))

type zWitness = z psatz

(** val zWeakChecker : z nFormula list -> z psatz -> bool **)

let zWeakChecker =
  check_normalised_formulas Z0 (Zpos XH) Z.add Z.mul zeq_bool Z.leb

(** val psub1 : z pol -> z pol -> z pol **)

let psub1 =
  psub0 Z0 Z.add Z.sub Z.opp zeq_bool

(** val padd1 : z pol -> z pol -> z pol **)

let padd1 =
  padd0 Z0 Z.add zeq_bool

(** val norm0 : z pExpr -> z pol **)

let norm0 =
  norm Z0 (Zpos XH) Z.add Z.mul Z.sub Z.opp zeq_bool

(** val xnormalise0 : z formula -> z nFormula list **)

let xnormalise0 t0 =
  let { flhs = lhs; fop = o; frhs = rhs } = t0 in
  let lhs0 = norm0 lhs in
  let rhs0 = norm0 rhs in
  (match o with
   | OpEq ->
     ((psub1 lhs0 (padd1 rhs0 (Pc (Zpos XH)))),NonStrict)::(((psub1 rhs0
                                                               (padd1 lhs0
                                                                 (Pc (Zpos
                                                                 XH)))),NonStrict)::[])
   | OpNEq -> ((psub1 lhs0 rhs0),Equal)::[]
   | OpLe -> ((psub1 lhs0 (padd1 rhs0 (Pc (Zpos XH)))),NonStrict)::[]
   | OpGe -> ((psub1 rhs0 (padd1 lhs0 (Pc (Zpos XH)))),NonStrict)::[]
   | OpLt -> ((psub1 lhs0 rhs0),NonStrict)::[]
   | OpGt -> ((psub1 rhs0 lhs0),NonStrict)::[])

(** val normalise : z formula -> z nFormula cnf **)

let normalise t0 =
  map (fun x -> x::[]) (xnormalise0 t0)

(** val xnegate0 : z formula -> z nFormula list **)

let xnegate0 t0 =
  let { flhs = lhs; fop = o; frhs = rhs } = t0 in
  let lhs0 = norm0 lhs in
  let rhs0 = norm0 rhs in
  (match o with
   | OpEq -> ((psub1 lhs0 rhs0),Equal)::[]
   | OpNEq ->
     ((psub1 lhs0 (padd1 rhs0 (Pc (Zpos XH)))),NonStrict)::(((psub1 rhs0
                                                               (padd1 lhs0
                                                                 (Pc (Zpos
                                                                 XH)))),NonStrict)::[])
   | OpLe -> ((psub1 rhs0 lhs0),NonStrict)::[]
   | OpGe -> ((psub1 lhs0 rhs0),NonStrict)::[]
   | OpLt -> ((psub1 rhs0 (padd1 lhs0 (Pc (Zpos XH)))),NonStrict)::[]
   | OpGt -> ((psub1 lhs0 (padd1 rhs0 (Pc (Zpos XH)))),NonStrict)::[])

(** val negate : z formula -> z nFormula cnf **)

let negate t0 =
  map (fun x -> x::[]) (xnegate0 t0)

(** val zunsat : z nFormula -> bool **)

let zunsat =
  check_inconsistent Z0 zeq_bool Z.leb

(** val zdeduce : z nFormula -> z nFormula -> z nFormula option **)

let zdeduce =
  nformula_plus_nformula Z0 Z.add zeq_bool

(** val ceiling : z -> z -> z **)

let ceiling a b =
  let q0,r = Z.div_eucl a b in
  (match r with
   | Z0 -> q0
   | _ -> Z.add q0 (Zpos XH))

type zArithProof =
| DoneProof
| RatProof of zWitness * zArithProof
| CutProof of zWitness * zArithProof
| EnumProof of zWitness * zWitness * zArithProof list

(** val zgcdM : z -> z -> z **)

let zgcdM x y =
  Z.max (Z.gcd x y) (Zpos XH)

(** val zgcd_pol : z polC -> z * z **)

let rec zgcd_pol = function
| Pc c -> Z0,c
| Pinj (_, p2) -> zgcd_pol p2
| PX (p2, _, q0) ->
  let g1,c1 = zgcd_pol p2 in
  let g2,c2 = zgcd_pol q0 in (zgcdM (zgcdM g1 c1) g2),c2

(** val zdiv_pol : z polC -> z -> z polC **)

let rec zdiv_pol p x =
  match p with
  | Pc c -> Pc (Z.div c x)
  | Pinj (j, p2) -> Pinj (j, (zdiv_pol p2 x))
  | PX (p2, j, q0) -> PX ((zdiv_pol p2 x), j, (zdiv_pol q0 x))

(** val makeCuttingPlane : z polC -> z polC * z **)

let makeCuttingPlane p =
  let g,c = zgcd_pol p in
  if Z.gtb g Z0
  then (zdiv_pol (psubC Z.sub p c) g),(Z.opp (ceiling (Z.opp c) g))
  else p,Z0

(** val genCuttingPlane : z nFormula -> ((z polC * z) * op1) option **)

let genCuttingPlane = function
| e,op ->
  (match op with
   | Equal ->
     let g,c = zgcd_pol e in
     if (&&) (Z.gtb g Z0)
          ((&&) (negb (zeq_bool c Z0)) (negb (zeq_bool (Z.gcd g c) g)))
     then None
     else Some ((makeCuttingPlane e),Equal)
   | NonEqual -> Some ((e,Z0),op)
   | Strict -> Some ((makeCuttingPlane (psubC Z.sub e (Zpos XH))),NonStrict)
   | NonStrict -> Some ((makeCuttingPlane e),NonStrict))

(** val nformula_of_cutting_plane : ((z polC * z) * op1) -> z nFormula **)

let nformula_of_cutting_plane = function
| e_z,o -> let e,z0 = e_z in (padd1 e (Pc z0)),o

(** val is_pol_Z0 : z polC -> bool **)

let is_pol_Z0 = function
| Pc z0 -> (match z0 with
            | Z0 -> true
            | _ -> false)
| _ -> false

(** val eval_Psatz0 : z nFormula list -> zWitness -> z nFormula option **)

let eval_Psatz0 =
  eval_Psatz Z0 (Zpos XH) Z.add Z.mul zeq_bool Z.leb

(** val valid_cut_sign : op1 -> bool **)

let valid_cut_sign = function
| Equal -> true
| NonStrict -> true
| _ -> false

(** val zChecker : z nFormula list -> zArithProof -> bool **)

let rec zChecker l = function
| DoneProof -> false
| RatProof (w, pf0) ->
  (match eval_Psatz0 l w with
   | Some f -> if zunsat f then true else zChecker (f::l) pf0
   | None -> false)
| CutProof (w, pf0) ->
  (match eval_Psatz0 l w with
   | Some f ->
     (match genCuttingPlane f with
      | Some cp -> zChecker ((nformula_of_cutting_plane cp)::l) pf0
      | None -> true)
   | None -> false)
| EnumProof (w1, w2, pf0) ->
  (match eval_Psatz0 l w1 with
   | Some f1 ->
     (match eval_Psatz0 l w2 with
      | Some f2 ->
        (match genCuttingPlane f1 with
         | Some p ->
           let p2,op3 = p in
           let e1,z1 = p2 in
           (match genCuttingPlane f2 with
            | Some p3 ->
              let p4,op4 = p3 in
              let e2,z2 = p4 in
              if (&&) ((&&) (valid_cut_sign op3) (valid_cut_sign op4))
                   (is_pol_Z0 (padd1 e1 e2))
              then let rec label pfs lb ub =
                     match pfs with
                     | [] -> Z.gtb lb ub
                     | pf1::rsr ->
                       (&&) (zChecker (((psub1 e1 (Pc lb)),Equal)::l) pf1)
                         (label rsr (Z.add lb (Zpos XH)) ub)
                   in label pf0 (Z.opp z1) z2
              else false
            | None -> true)
         | None -> true)
      | None -> false)
   | None -> false)

(** val zTautoChecker : z formula bFormula -> zArithProof list -> bool **)

let zTautoChecker f w =
  tauto_checker zunsat zdeduce normalise negate zChecker f w

type qWitness = q psatz

(** val qWeakChecker : q nFormula list -> q psatz -> bool **)

let qWeakChecker =
  check_normalised_formulas { qnum = Z0; qden = XH } { qnum = (Zpos XH);
    qden = XH } qplus qmult qeq_bool qle_bool

(** val qnormalise : q formula -> q nFormula cnf **)

let qnormalise =
  cnf_normalise { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH }
    qplus qmult qminus qopp qeq_bool

(** val qnegate : q formula -> q nFormula cnf **)

let qnegate =
  cnf_negate { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH } qplus
    qmult qminus qopp qeq_bool

(** val qunsat : q nFormula -> bool **)

let qunsat =
  check_inconsistent { qnum = Z0; qden = XH } qeq_bool qle_bool

(** val qdeduce : q nFormula -> q nFormula -> q nFormula option **)

let qdeduce =
  nformula_plus_nformula { qnum = Z0; qden = XH } qplus qeq_bool

(** val qTautoChecker : q formula bFormula -> qWitness list -> bool **)

let qTautoChecker f w =
  tauto_checker qunsat qdeduce qnormalise qnegate qWeakChecker f w

type rcst =
| C0
| C1
| CQ of q
| CZ of z
| CPlus of rcst * rcst
| CMinus of rcst * rcst
| CMult of rcst * rcst
| CInv of rcst
| COpp of rcst

(** val q_of_Rcst : rcst -> q **)

let rec q_of_Rcst = function
| C0 -> { qnum = Z0; qden = XH }
| C1 -> { qnum = (Zpos XH); qden = XH }
| CQ q0 -> q0
| CZ z0 -> { qnum = z0; qden = XH }
| CPlus (r1, r2) -> qplus (q_of_Rcst r1) (q_of_Rcst r2)
| CMinus (r1, r2) -> qminus (q_of_Rcst r1) (q_of_Rcst r2)
| CMult (r1, r2) -> qmult (q_of_Rcst r1) (q_of_Rcst r2)
| CInv r0 -> qinv (q_of_Rcst r0)
| COpp r0 -> qopp (q_of_Rcst r0)

type rWitness = q psatz

(** val rWeakChecker : q nFormula list -> q psatz -> bool **)

let rWeakChecker =
  check_normalised_formulas { qnum = Z0; qden = XH } { qnum = (Zpos XH);
    qden = XH } qplus qmult qeq_bool qle_bool

(** val rnormalise : q formula -> q nFormula cnf **)

let rnormalise =
  cnf_normalise { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH }
    qplus qmult qminus qopp qeq_bool

(** val rnegate : q formula -> q nFormula cnf **)

let rnegate =
  cnf_negate { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH } qplus
    qmult qminus qopp qeq_bool

(** val runsat : q nFormula -> bool **)

let runsat =
  check_inconsistent { qnum = Z0; qden = XH } qeq_bool qle_bool

(** val rdeduce : q nFormula -> q nFormula -> q nFormula option **)

let rdeduce =
  nformula_plus_nformula { qnum = Z0; qden = XH } qplus qeq_bool

(** val rTautoChecker : rcst formula bFormula -> rWitness list -> bool **)

let rTautoChecker f w =
  tauto_checker runsat rdeduce rnormalise rnegate rWeakChecker
    (map_bformula (map_Formula q_of_Rcst) f) w
