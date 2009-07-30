(** val negb : bool -> bool **)

let negb = function
  | true -> false
  | false -> true

type nat =
  | O
  | S of nat

type comparison =
  | Eq
  | Lt
  | Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
  | Eq -> Eq
  | Lt -> Gt
  | Gt -> Lt

(** val plus : nat -> nat -> nat **)

let rec plus n0 m =
  match n0 with
    | O -> m
    | S p -> S (plus p m)

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
    | [] -> m
    | a :: l1 -> a :: (app l1 m)

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n0 l default =
  match n0 with
    | O -> (match l with
              | [] -> default
              | x :: l' -> x)
    | S m -> (match l with
                | [] -> default
                | x :: t0 -> nth m t0 default)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
  | [] -> []
  | a :: t0 -> (f a) :: (map f t0)

type positive =
  | XI of positive
  | XO of positive
  | XH

(** val psucc : positive -> positive **)

let rec psucc = function
  | XI p -> XO (psucc p)
  | XO p -> XI p
  | XH -> XO XH

(** val pplus : positive -> positive -> positive **)

let rec pplus x y =
  match x with
    | XI p ->
        (match y with
           | XI q0 -> XO (pplus_carry p q0)
           | XO q0 -> XI (pplus p q0)
           | XH -> XO (psucc p))
    | XO p ->
        (match y with
           | XI q0 -> XI (pplus p q0)
           | XO q0 -> XO (pplus p q0)
           | XH -> XI p)
    | XH ->
        (match y with
           | XI q0 -> XO (psucc q0)
           | XO q0 -> XI q0
           | XH -> XO XH)

(** val pplus_carry : positive -> positive -> positive **)

and pplus_carry x y =
  match x with
    | XI p ->
        (match y with
           | XI q0 -> XI (pplus_carry p q0)
           | XO q0 -> XO (pplus_carry p q0)
           | XH -> XI (psucc p))
    | XO p ->
        (match y with
           | XI q0 -> XO (pplus_carry p q0)
           | XO q0 -> XI (pplus p q0)
           | XH -> XO (psucc p))
    | XH ->
        (match y with
           | XI q0 -> XI (psucc q0)
           | XO q0 -> XO (psucc q0)
           | XH -> XI XH)

(** val p_of_succ_nat : nat -> positive **)

let rec p_of_succ_nat = function
  | O -> XH
  | S x -> psucc (p_of_succ_nat x)

(** val pdouble_minus_one : positive -> positive **)

let rec pdouble_minus_one = function
  | XI p -> XI (XO p)
  | XO p -> XI (pdouble_minus_one p)
  | XH -> XH

type positive_mask =
  | IsNul
  | IsPos of positive
  | IsNeg

(** val pdouble_plus_one_mask : positive_mask -> positive_mask **)

let pdouble_plus_one_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

(** val pdouble_mask : positive_mask -> positive_mask **)

let pdouble_mask = function
  | IsNul -> IsNul
  | IsPos p -> IsPos (XO p)
  | IsNeg -> IsNeg

(** val pdouble_minus_two : positive -> positive_mask **)

let pdouble_minus_two = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pdouble_minus_one p))
  | XH -> IsNul

(** val pminus_mask : positive -> positive -> positive_mask **)

let rec pminus_mask x y =
  match x with
    | XI p ->
        (match y with
           | XI q0 -> pdouble_mask (pminus_mask p q0)
           | XO q0 -> pdouble_plus_one_mask (pminus_mask p q0)
           | XH -> IsPos (XO p))
    | XO p ->
        (match y with
           | XI q0 -> pdouble_plus_one_mask (pminus_mask_carry p q0)
           | XO q0 -> pdouble_mask (pminus_mask p q0)
           | XH -> IsPos (pdouble_minus_one p))
    | XH -> (match y with
               | XH -> IsNul
               | _ -> IsNeg)

(** val pminus_mask_carry : positive -> positive -> positive_mask **)

and pminus_mask_carry x y =
  match x with
    | XI p ->
        (match y with
           | XI q0 -> pdouble_plus_one_mask (pminus_mask_carry p q0)
           | XO q0 -> pdouble_mask (pminus_mask p q0)
           | XH -> IsPos (pdouble_minus_one p))
    | XO p ->
        (match y with
           | XI q0 -> pdouble_mask (pminus_mask_carry p q0)
           | XO q0 -> pdouble_plus_one_mask (pminus_mask_carry p q0)
           | XH -> pdouble_minus_two p)
    | XH -> IsNeg

(** val pminus : positive -> positive -> positive **)

let pminus x y =
  match pminus_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

(** val pmult : positive -> positive -> positive **)

let rec pmult x y =
  match x with
    | XI p -> pplus y (XO (pmult p y))
    | XO p -> XO (pmult p y)
    | XH -> y

(** val pcompare : positive -> positive -> comparison -> comparison **)

let rec pcompare x y r =
  match x with
    | XI p ->
        (match y with
           | XI q0 -> pcompare p q0 r
           | XO q0 -> pcompare p q0 Gt
           | XH -> Gt)
    | XO p ->
        (match y with
           | XI q0 -> pcompare p q0 Lt
           | XO q0 -> pcompare p q0 r
           | XH -> Gt)
    | XH -> (match y with
               | XH -> r
               | _ -> Lt)

(** val psize : positive -> nat **)

let rec psize = function
  | XI p2 -> S (psize p2)
  | XO p2 -> S (psize p2)
  | XH -> S O

type n =
  | N0
  | Npos of positive

type z =
  | Z0
  | Zpos of positive
  | Zneg of positive

(** val zdouble_plus_one : z -> z **)

let zdouble_plus_one = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (pdouble_minus_one p)

(** val zdouble_minus_one : z -> z **)

let zdouble_minus_one = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (pdouble_minus_one p)
  | Zneg p -> Zneg (XI p)

(** val zdouble : z -> z **)

let zdouble = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

(** val zPminus : positive -> positive -> z **)

let rec zPminus x y =
  match x with
    | XI p ->
        (match y with
           | XI q0 -> zdouble (zPminus p q0)
           | XO q0 -> zdouble_plus_one (zPminus p q0)
           | XH -> Zpos (XO p))
    | XO p ->
        (match y with
           | XI q0 -> zdouble_minus_one (zPminus p q0)
           | XO q0 -> zdouble (zPminus p q0)
           | XH -> Zpos (pdouble_minus_one p))
    | XH ->
        (match y with
           | XI q0 -> Zneg (XO q0)
           | XO q0 -> Zneg (pdouble_minus_one q0)
           | XH -> Z0)

(** val zplus : z -> z -> z **)

let zplus x y =
  match x with
    | Z0 -> y
    | Zpos x' ->
        (match y with
           | Z0 -> Zpos x'
           | Zpos y' -> Zpos (pplus x' y')
           | Zneg y' ->
               (match pcompare x' y' Eq with
                  | Eq -> Z0
                  | Lt -> Zneg (pminus y' x')
                  | Gt -> Zpos (pminus x' y')))
    | Zneg x' ->
        (match y with
           | Z0 -> Zneg x'
           | Zpos y' ->
               (match pcompare x' y' Eq with
                  | Eq -> Z0
                  | Lt -> Zpos (pminus y' x')
                  | Gt -> Zneg (pminus x' y'))
           | Zneg y' -> Zneg (pplus x' y'))

(** val zopp : z -> z **)

let zopp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

(** val zminus : z -> z -> z **)

let zminus m n0 =
  zplus m (zopp n0)

(** val zmult : z -> z -> z **)

let zmult x y =
  match x with
    | Z0 -> Z0
    | Zpos x' ->
        (match y with
           | Z0 -> Z0
           | Zpos y' -> Zpos (pmult x' y')
           | Zneg y' -> Zneg (pmult x' y'))
    | Zneg x' ->
        (match y with
           | Z0 -> Z0
           | Zpos y' -> Zneg (pmult x' y')
           | Zneg y' -> Zpos (pmult x' y'))

(** val zcompare : z -> z -> comparison **)

let zcompare x y =
  match x with
    | Z0 -> (match y with
               | Z0 -> Eq
               | Zpos y' -> Lt
               | Zneg y' -> Gt)
    | Zpos x' -> (match y with
                    | Zpos y' -> pcompare x' y' Eq
                    | _ -> Gt)
    | Zneg x' ->
        (match y with
           | Zneg y' -> compOpp (pcompare x' y' Eq)
           | _ -> Lt)

(** val zabs : z -> z **)

let zabs = function
  | Z0 -> Z0
  | Zpos p -> Zpos p
  | Zneg p -> Zpos p

(** val z_gt_dec : z -> z -> bool **)

let z_gt_dec x y =
  match zcompare x y with
    | Gt -> true
    | _ -> false

(** val zle_bool : z -> z -> bool **)

let zle_bool x y =
  match zcompare x y with
    | Gt -> false
    | _ -> true

(** val zge_bool : z -> z -> bool **)

let zge_bool x y =
  match zcompare x y with
    | Lt -> false
    | _ -> true

(** val zgt_bool : z -> z -> bool **)

let zgt_bool x y =
  match zcompare x y with
    | Gt -> true
    | _ -> false

(** val zeq_bool : z -> z -> bool **)

let zeq_bool x y =
  match zcompare x y with
    | Eq -> true
    | _ -> false

(** val n_of_nat : nat -> n **)

let n_of_nat = function
  | O -> N0
  | S n' -> Npos (p_of_succ_nat n')

(** val zdiv_eucl_POS : positive -> z -> z  *  z **)

let rec zdiv_eucl_POS a b =
  match a with
    | XI a' ->
        let q0 , r = zdiv_eucl_POS a' b in
        let r' = zplus (zmult (Zpos (XO XH)) r) (Zpos XH) in
        if zgt_bool b r'
        then (zmult (Zpos (XO XH)) q0) , r'
        else (zplus (zmult (Zpos (XO XH)) q0) (Zpos XH)) , (zminus r' b)
    | XO a' ->
        let q0 , r = zdiv_eucl_POS a' b in
        let r' = zmult (Zpos (XO XH)) r in
        if zgt_bool b r'
        then (zmult (Zpos (XO XH)) q0) , r'
        else (zplus (zmult (Zpos (XO XH)) q0) (Zpos XH)) , (zminus r' b)
    | XH ->
        if zge_bool b (Zpos (XO XH)) then Z0 , (Zpos XH) else (Zpos XH) , Z0

(** val zdiv_eucl : z -> z -> z  *  z **)

let zdiv_eucl a b =
  match a with
    | Z0 -> Z0 , Z0
    | Zpos a' ->
        (match b with
           | Z0 -> Z0 , Z0
           | Zpos p -> zdiv_eucl_POS a' b
           | Zneg b' ->
               let q0 , r = zdiv_eucl_POS a' (Zpos b') in
               (match r with
                  | Z0 -> (zopp q0) , Z0
                  | _ -> (zopp (zplus q0 (Zpos XH))) , (zplus b r)))
    | Zneg a' ->
        (match b with
           | Z0 -> Z0 , Z0
           | Zpos p ->
               let q0 , r = zdiv_eucl_POS a' b in
               (match r with
                  | Z0 -> (zopp q0) , Z0
                  | _ -> (zopp (zplus q0 (Zpos XH))) , (zminus b r))
           | Zneg b' ->
               let q0 , r = zdiv_eucl_POS a' (Zpos b') in q0 , (zopp r))

(** val zdiv : z -> z -> z **)

let zdiv a b =
  let q0 , x = zdiv_eucl a b in q0

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
               (match pcompare j j' Eq with
                  | Eq -> peq ceqb q0 q'
                  | _ -> false)
           | _ -> false)
    | PX (p2, i, q0) ->
        (match p' with
           | PX (p'0, i', q') ->
               (match pcompare i i' Eq with
                  | Eq -> if peq ceqb p2 p'0 then peq ceqb q0 q' else false
                  | _ -> false)
           | _ -> false)

(** val mkPinj_pred : positive -> 'a1 pol -> 'a1 pol **)

let mkPinj_pred j p =
  match j with
    | XI j0 -> Pinj ((XO j0), p)
    | XO j0 -> Pinj ((pdouble_minus_one j0), p)
    | XH -> p

(** val mkPX :
    'a1 -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol **)

let mkPX cO ceqb p i q0 =
  match p with
    | Pc c ->
        if ceqb c cO
        then (match q0 with
                | Pc c0 -> q0
                | Pinj (j', q1) -> Pinj ((pplus XH j'), q1)
                | PX (p2, p3, p4) -> Pinj (XH, q0))
        else PX (p, i, q0)
    | Pinj (p2, p3) -> PX (p, i, q0)
    | PX (p', i', q') ->
        if peq ceqb q' (p0 cO)
        then PX (p', (pplus i' i), q0)
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
  | Pc c ->
      let p2 = paddC cadd q0 c in
      (match p2 with
         | Pc c0 -> p2
         | Pinj (j', q1) -> Pinj ((pplus j j'), q1)
         | PX (p3, p4, p5) -> Pinj (j, p2))
  | Pinj (j', q') ->
      (match zPminus j' j with
         | Z0 ->
             let p2 = pop q' q0 in
             (match p2 with
                | Pc c -> p2
                | Pinj (j'0, q1) -> Pinj ((pplus j j'0), q1)
                | PX (p3, p4, p5) -> Pinj (j, p2))
         | Zpos k ->
             let p2 = pop (Pinj (k, q')) q0 in
             (match p2 with
                | Pc c -> p2
                | Pinj (j'0, q1) -> Pinj ((pplus j j'0), q1)
                | PX (p3, p4, p5) -> Pinj (j, p2))
         | Zneg k ->
             let p2 = paddI cadd pop q0 k q' in
             (match p2 with
                | Pc c -> p2
                | Pinj (j'0, q1) -> Pinj ((pplus j' j'0), q1)
                | PX (p3, p4, p5) -> Pinj (j', p2)))
  | PX (p2, i, q') ->
      (match j with
         | XI j0 -> PX (p2, i, (paddI cadd pop q0 (XO j0) q'))
         | XO j0 -> PX (p2, i, (paddI cadd pop q0 (pdouble_minus_one j0) q'))
         | XH -> PX (p2, i, (pop q' q0)))

(** val psubI :
    ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 pol -> 'a1 pol -> 'a1 pol) ->
    'a1 pol -> positive -> 'a1 pol -> 'a1 pol **)

let rec psubI cadd copp pop q0 j = function
  | Pc c ->
      let p2 = paddC cadd (popp copp q0) c in
      (match p2 with
         | Pc c0 -> p2
         | Pinj (j', q1) -> Pinj ((pplus j j'), q1)
         | PX (p3, p4, p5) -> Pinj (j, p2))
  | Pinj (j', q') ->
      (match zPminus j' j with
         | Z0 ->
             let p2 = pop q' q0 in
             (match p2 with
                | Pc c -> p2
                | Pinj (j'0, q1) -> Pinj ((pplus j j'0), q1)
                | PX (p3, p4, p5) -> Pinj (j, p2))
         | Zpos k ->
             let p2 = pop (Pinj (k, q')) q0 in
             (match p2 with
                | Pc c -> p2
                | Pinj (j'0, q1) -> Pinj ((pplus j j'0), q1)
                | PX (p3, p4, p5) -> Pinj (j, p2))
         | Zneg k ->
             let p2 = psubI cadd copp pop q0 k q' in
             (match p2 with
                | Pc c -> p2
                | Pinj (j'0, q1) -> Pinj ((pplus j' j'0), q1)
                | PX (p3, p4, p5) -> Pinj (j', p2)))
  | PX (p2, i, q') ->
      (match j with
         | XI j0 -> PX (p2, i, (psubI cadd copp pop q0 (XO j0) q'))
         | XO j0 -> PX (p2, i,
             (psubI cadd copp pop q0 (pdouble_minus_one j0) q'))
         | XH -> PX (p2, i, (pop q' q0)))

(** val paddX :
    'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol
    -> positive -> 'a1 pol -> 'a1 pol **)

let rec paddX cO ceqb pop p' i' p = match p with
  | Pc c -> PX (p', i', p)
  | Pinj (j, q') ->
      (match j with
         | XI j0 -> PX (p', i', (Pinj ((XO j0), q')))
         | XO j0 -> PX (p', i', (Pinj ((pdouble_minus_one j0), q')))
         | XH -> PX (p', i', q'))
  | PX (p2, i, q') ->
      (match zPminus i i' with
         | Z0 -> mkPX cO ceqb (pop p2 p') i q'
         | Zpos k -> mkPX cO ceqb (pop (PX (p2, k, (p0 cO))) p') i' q'
         | Zneg k -> mkPX cO ceqb (paddX cO ceqb pop p' k p2) i q')

(** val psubX :
    'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol -> 'a1
    pol) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol **)

let rec psubX cO copp ceqb pop p' i' p = match p with
  | Pc c -> PX ((popp copp p'), i', p)
  | Pinj (j, q') ->
      (match j with
         | XI j0 -> PX ((popp copp p'), i', (Pinj ((XO j0), q')))
         | XO j0 -> PX ((popp copp p'), i', (Pinj (
             (pdouble_minus_one j0), q')))
         | XH -> PX ((popp copp p'), i', q'))
  | PX (p2, i, q') ->
      (match zPminus i i' with
         | Z0 -> mkPX cO ceqb (pop p2 p') i q'
         | Zpos k -> mkPX cO ceqb (pop (PX (p2, k, (p0 cO))) p') i' q'
         | Zneg k -> mkPX cO ceqb (psubX cO copp ceqb pop p' k p2) i q')

(** val padd :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol
    -> 'a1 pol **)

let rec padd cO cadd ceqb p = function
  | Pc c' -> paddC cadd p c'
  | Pinj (j', q') -> paddI cadd (fun x x0 -> padd cO cadd ceqb x x0) q' j' p
  | PX (p'0, i', q') ->
      (match p with
         | Pc c -> PX (p'0, i', (paddC cadd q' c))
         | Pinj (j, q0) ->
             (match j with
                | XI j0 -> PX (p'0, i',
                    (padd cO cadd ceqb (Pinj ((XO j0), q0)) q'))
                | XO j0 -> PX (p'0, i',
                    (padd cO cadd ceqb (Pinj ((pdouble_minus_one j0), q0))
                      q'))
                | XH -> PX (p'0, i', (padd cO cadd ceqb q0 q')))
         | PX (p2, i, q0) ->
             (match zPminus i i' with
                | Z0 ->
                    mkPX cO ceqb (padd cO cadd ceqb p2 p'0) i
                      (padd cO cadd ceqb q0 q')
                | Zpos k ->
                    mkPX cO ceqb
                      (padd cO cadd ceqb (PX (p2, k, (p0 cO))) p'0) i'
                      (padd cO cadd ceqb q0 q')
                | Zneg k ->
                    mkPX cO ceqb
                      (paddX cO ceqb (fun x x0 -> padd cO cadd ceqb x x0) p'0
                        k p2) i (padd cO cadd ceqb q0 q')))

(** val psub :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1
    -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol **)

let rec psub cO cadd csub copp ceqb p = function
  | Pc c' -> psubC csub p c'
  | Pinj (j', q') ->
      psubI cadd copp (fun x x0 -> psub cO cadd csub copp ceqb x x0) q' j' p
  | PX (p'0, i', q') ->
      (match p with
         | Pc c -> PX ((popp copp p'0), i', (paddC cadd (popp copp q') c))
         | Pinj (j, q0) ->
             (match j with
                | XI j0 -> PX ((popp copp p'0), i',
                    (psub cO cadd csub copp ceqb (Pinj ((XO j0), q0)) q'))
                | XO j0 -> PX ((popp copp p'0), i',
                    (psub cO cadd csub copp ceqb (Pinj
                      ((pdouble_minus_one j0), q0)) q'))
                | XH -> PX ((popp copp p'0), i',
                    (psub cO cadd csub copp ceqb q0 q')))
         | PX (p2, i, q0) ->
             (match zPminus i i' with
                | Z0 ->
                    mkPX cO ceqb (psub cO cadd csub copp ceqb p2 p'0) i
                      (psub cO cadd csub copp ceqb q0 q')
                | Zpos k ->
                    mkPX cO ceqb
                      (psub cO cadd csub copp ceqb (PX (p2, k, (p0 cO))) p'0)
                      i' (psub cO cadd csub copp ceqb q0 q')
                | Zneg k ->
                    mkPX cO ceqb
                      (psubX cO copp ceqb (fun x x0 ->
                        psub cO cadd csub copp ceqb x x0) p'0 k p2) i
                      (psub cO cadd csub copp ceqb q0 q')))

(** val pmulC_aux :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 ->
    'a1 pol **)

let rec pmulC_aux cO cmul ceqb p c =
  match p with
    | Pc c' -> Pc (cmul c' c)
    | Pinj (j, q0) ->
        let p2 = pmulC_aux cO cmul ceqb q0 c in
        (match p2 with
           | Pc c0 -> p2
           | Pinj (j', q1) -> Pinj ((pplus j j'), q1)
           | PX (p3, p4, p5) -> Pinj (j, p2))
    | PX (p2, i, q0) ->
        mkPX cO ceqb (pmulC_aux cO cmul ceqb p2 c) i
          (pmulC_aux cO cmul ceqb q0 c)

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
  | Pc c ->
      let p2 = pmulC cO cI cmul ceqb q0 c in
      (match p2 with
         | Pc c0 -> p2
         | Pinj (j', q1) -> Pinj ((pplus j j'), q1)
         | PX (p3, p4, p5) -> Pinj (j, p2))
  | Pinj (j', q') ->
      (match zPminus j' j with
         | Z0 ->
             let p2 = pmul0 q' q0 in
             (match p2 with
                | Pc c -> p2
                | Pinj (j'0, q1) -> Pinj ((pplus j j'0), q1)
                | PX (p3, p4, p5) -> Pinj (j, p2))
         | Zpos k ->
             let p2 = pmul0 (Pinj (k, q')) q0 in
             (match p2 with
                | Pc c -> p2
                | Pinj (j'0, q1) -> Pinj ((pplus j j'0), q1)
                | PX (p3, p4, p5) -> Pinj (j, p2))
         | Zneg k ->
             let p2 = pmulI cO cI cmul ceqb pmul0 q0 k q' in
             (match p2 with
                | Pc c -> p2
                | Pinj (j'0, q1) -> Pinj ((pplus j' j'0), q1)
                | PX (p3, p4, p5) -> Pinj (j', p2)))
  | PX (p', i', q') ->
      (match j with
         | XI j' ->
             mkPX cO ceqb (pmulI cO cI cmul ceqb pmul0 q0 j p') i'
               (pmulI cO cI cmul ceqb pmul0 q0 (XO j') q')
         | XO j' ->
             mkPX cO ceqb (pmulI cO cI cmul ceqb pmul0 q0 j p') i'
               (pmulI cO cI cmul ceqb pmul0 q0 (pdouble_minus_one j') q')
         | XH ->
             mkPX cO ceqb (pmulI cO cI cmul ceqb pmul0 q0 XH p') i'
               (pmul0 q' q0))

(** val pmul :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol **)

let rec pmul cO cI cadd cmul ceqb p p'' = match p'' with
  | Pc c -> pmulC cO cI cmul ceqb p c
  | Pinj (j', q') ->
      pmulI cO cI cmul ceqb (fun x x0 -> pmul cO cI cadd cmul ceqb x x0) q'
        j' p
  | PX (p', i', q') ->
      (match p with
         | Pc c -> pmulC cO cI cmul ceqb p'' c
         | Pinj (j, q0) ->
             mkPX cO ceqb (pmul cO cI cadd cmul ceqb p p') i'
               (match j with
                  | XI j0 ->
                      pmul cO cI cadd cmul ceqb (Pinj ((XO j0), q0)) q'
                  | XO j0 ->
                      pmul cO cI cadd cmul ceqb (Pinj
                        ((pdouble_minus_one j0), q0)) q'
                  | XH -> pmul cO cI cadd cmul ceqb q0 q')
         | PX (p2, i, q0) ->
             padd cO cadd ceqb
               (mkPX cO ceqb
                 (padd cO cadd ceqb
                   (mkPX cO ceqb (pmul cO cI cadd cmul ceqb p2 p') i (p0 cO))
                   (pmul cO cI cadd cmul ceqb
                     (match q0 with
                        | Pc c -> q0
                        | Pinj (j', q1) -> Pinj ((pplus XH j'), q1)
                        | PX (p3, p4, p5) -> Pinj (XH, q0)) p')) i' 
                 (p0 cO))
               (mkPX cO ceqb
                 (pmulI cO cI cmul ceqb (fun x x0 ->
                   pmul cO cI cadd cmul ceqb x x0) q' XH p2) i
                 (pmul cO cI cadd cmul ceqb q0 q')))

(** val psquare :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> 'a1 pol -> 'a1 pol **)

let rec psquare cO cI cadd cmul ceqb = function
  | Pc c -> Pc (cmul c c)
  | Pinj (j, q0) -> Pinj (j, (psquare cO cI cadd cmul ceqb q0))
  | PX (p2, i, q0) ->
      mkPX cO ceqb
        (padd cO cadd ceqb
          (mkPX cO ceqb (psquare cO cI cadd cmul ceqb p2) i (p0 cO))
          (pmul cO cI cadd cmul ceqb p2
            (let p3 = pmulC cO cI cmul ceqb q0 (cadd cI cI) in
            match p3 with
              | Pc c -> p3
              | Pinj (j', q1) -> Pinj ((pplus XH j'), q1)
              | PX (p4, p5, p6) -> Pinj (XH, p3)))) i
        (psquare cO cI cadd cmul ceqb q0)

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
                    padd cO cadd ceqb
                      (norm_aux cO cI cadd cmul csub copp ceqb pe1)
                      (norm_aux cO cI cadd cmul csub copp ceqb pe2)))
  | PEsub (pe1, pe2) ->
      psub cO cadd csub copp ceqb
        (norm_aux cO cI cadd cmul csub copp ceqb pe1)
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

type 'term' clause = 'term' list

type 'term' cnf = 'term' clause list

(** val tt : 'a1 cnf **)

let tt =
  []

(** val ff : 'a1 cnf **)

let ff =
  [] :: []

(** val or_clause_cnf : 'a1 clause -> 'a1 cnf -> 'a1 cnf **)

let or_clause_cnf t0 f =
  map (fun x -> app t0 x) f

(** val or_cnf : 'a1 cnf -> 'a1 cnf -> 'a1 cnf **)

let rec or_cnf f f' =
  match f with
    | [] -> tt
    | e :: rst -> app (or_cnf rst f') (or_clause_cnf e f')

(** val and_cnf : 'a1 cnf -> 'a1 cnf -> 'a1 cnf **)

let and_cnf f1 f2 =
  app f1 f2

(** val xcnf :
    ('a1 -> 'a2 cnf) -> ('a1 -> 'a2 cnf) -> bool -> 'a1 bFormula -> 'a2 cnf **)

let rec xcnf normalise0 negate0 pol0 = function
  | TT -> if pol0 then tt else ff
  | FF -> if pol0 then ff else tt
  | X -> ff
  | A x -> if pol0 then normalise0 x else negate0 x
  | Cj (e1, e2) ->
      if pol0
      then and_cnf (xcnf normalise0 negate0 pol0 e1)
             (xcnf normalise0 negate0 pol0 e2)
      else or_cnf (xcnf normalise0 negate0 pol0 e1)
             (xcnf normalise0 negate0 pol0 e2)
  | D (e1, e2) ->
      if pol0
      then or_cnf (xcnf normalise0 negate0 pol0 e1)
             (xcnf normalise0 negate0 pol0 e2)
      else and_cnf (xcnf normalise0 negate0 pol0 e1)
             (xcnf normalise0 negate0 pol0 e2)
  | N e -> xcnf normalise0 negate0 (negb pol0) e
  | I (e1, e2) ->
      if pol0
      then or_cnf (xcnf normalise0 negate0 (negb pol0) e1)
             (xcnf normalise0 negate0 pol0 e2)
      else and_cnf (xcnf normalise0 negate0 (negb pol0) e1)
             (xcnf normalise0 negate0 pol0 e2)

(** val cnf_checker :
    ('a1 list -> 'a2 -> bool) -> 'a1 cnf -> 'a2 list -> bool **)

let rec cnf_checker checker f l =
  match f with
    | [] -> true
    | e :: f0 ->
        (match l with
           | [] -> false
           | c :: l0 ->
               if checker e c then cnf_checker checker f0 l0 else false)

(** val tauto_checker :
    ('a1 -> 'a2 cnf) -> ('a1 -> 'a2 cnf) -> ('a2 list -> 'a3 -> bool) -> 'a1
    bFormula -> 'a3 list -> bool **)

let tauto_checker normalise0 negate0 checker f w =
  cnf_checker checker (xcnf normalise0 negate0 true f) w

type 'c polC = 'c pol

type op1 =
  | Equal
  | NonEqual
  | Strict
  | NonStrict

type 'c nFormula = 'c polC  *  op1

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
           | NonEqual -> None
           | Strict -> Some Strict
           | _ -> Some NonStrict)

type 'c psatz =
  | PsatzIn of nat
  | PsatzSquare of 'c polC
  | PsatzMulC of 'c polC * 'c psatz
  | PsatzMulE of 'c psatz * 'c psatz
  | PsatzAdd of 'c psatz * 'c psatz
  | PsatzC of 'c
  | PsatzZ

(** val pexpr_times_nformula :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> 'a1 polC -> 'a1 nFormula -> 'a1 nFormula option **)

let pexpr_times_nformula cO cI cplus ctimes ceqb e = function
  | ef , o ->
      (match o with
         | Equal -> Some ((pmul cO cI cplus ctimes ceqb e ef) , Equal)
         | _ -> None)

(** val nformula_times_nformula :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> 'a1 nFormula -> 'a1 nFormula -> 'a1 nFormula option **)

let nformula_times_nformula cO cI cplus ctimes ceqb f1 f2 =
  let e1 , o1 = f1 in
  let e2 , o2 = f2 in
  (match o1 with
     | Equal -> Some ((pmul cO cI cplus ctimes ceqb e1 e2) , Equal)
     | NonEqual ->
         (match o2 with
            | Equal -> Some ((pmul cO cI cplus ctimes ceqb e1 e2) , Equal)
            | NonEqual -> Some ((pmul cO cI cplus ctimes ceqb e1 e2) ,
                NonEqual)
            | _ -> None)
     | Strict ->
         (match o2 with
            | NonEqual -> None
            | _ -> Some ((pmul cO cI cplus ctimes ceqb e1 e2) , o2))
     | NonStrict ->
         (match o2 with
            | Equal -> Some ((pmul cO cI cplus ctimes ceqb e1 e2) , Equal)
            | NonEqual -> None
            | _ -> Some ((pmul cO cI cplus ctimes ceqb e1 e2) , NonStrict)))

(** val nformula_plus_nformula :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula -> 'a1
    nFormula -> 'a1 nFormula option **)

let nformula_plus_nformula cO cplus ceqb f1 f2 =
  let e1 , o1 = f1 in
  let e2 , o2 = f2 in
  (match opAdd o1 o2 with
     | Some x -> Some ((padd cO cplus ceqb e1 e2) , x)
     | None -> None)

(** val eval_Psatz :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula list -> 'a1 psatz -> 'a1
    nFormula option **)

let rec eval_Psatz cO cI cplus ctimes ceqb cleb l = function
  | PsatzIn n0 -> Some (nth n0 l ((Pc cO) , Equal))
  | PsatzSquare e0 -> Some ((psquare cO cI cplus ctimes ceqb e0) , NonStrict)
  | PsatzMulC (re, e0) ->
      (match eval_Psatz cO cI cplus ctimes ceqb cleb l e0 with
         | Some x -> pexpr_times_nformula cO cI cplus ctimes ceqb re x
         | None -> None)
  | PsatzMulE (f1, f2) ->
      (match eval_Psatz cO cI cplus ctimes ceqb cleb l f1 with
         | Some x ->
             (match eval_Psatz cO cI cplus ctimes ceqb cleb l f2 with
                | Some x' ->
                    nformula_times_nformula cO cI cplus ctimes ceqb x x'
                | None -> None)
         | None -> None)
  | PsatzAdd (f1, f2) ->
      (match eval_Psatz cO cI cplus ctimes ceqb cleb l f1 with
         | Some x ->
             (match eval_Psatz cO cI cplus ctimes ceqb cleb l f2 with
                | Some x' -> nformula_plus_nformula cO cplus ceqb x x'
                | None -> None)
         | None -> None)
  | PsatzC c ->
      if (&&) (cleb cO c) (negb (ceqb cO c))
      then Some ((Pc c) , Strict)
      else None
  | PsatzZ -> Some ((Pc cO) , Equal)

(** val check_inconsistent :
    'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula ->
    bool **)

let check_inconsistent cO ceqb cleb = function
  | e , op ->
      (match e with
         | Pc c ->
             (match op with
                | Equal -> negb (ceqb c cO)
                | NonEqual -> ceqb c cO
                | Strict -> cleb c cO
                | NonStrict -> (&&) (cleb c cO) (negb (ceqb c cO)))
         | _ -> false)

(** val check_normalised_formulas :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula list -> 'a1 psatz ->
    bool **)

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

type 'c formula = { flhs : 'c pExpr; fop : op2; frhs : 'c pExpr }

(** val flhs : 'a1 formula -> 'a1 pExpr **)

let flhs x = x.flhs

(** val fop : 'a1 formula -> op2 **)

let fop x = x.fop

(** val frhs : 'a1 formula -> 'a1 pExpr **)

let frhs x = x.frhs

(** val norm :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pExpr -> 'a1 pol **)

let norm cO cI cplus ctimes cminus copp ceqb pe =
  norm_aux cO cI cplus ctimes cminus copp ceqb pe

(** val psub0 :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1
    -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol **)

let psub0 cO cplus cminus copp ceqb p p' =
  psub cO cplus cminus copp ceqb p p'

(** val padd0 :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol
    -> 'a1 pol **)

let padd0 cO cplus ceqb p p' =
  padd cO cplus ceqb p p'

(** val xnormalise :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 formula -> 'a1
    nFormula list **)

let xnormalise cO cI cplus ctimes cminus copp ceqb t0 =
  let { flhs = lhs; fop = o; frhs = rhs } = t0 in
  let lhs0 = norm cO cI cplus ctimes cminus copp ceqb lhs in
  let rhs0 = norm cO cI cplus ctimes cminus copp ceqb rhs in
  (match o with
     | OpEq -> ((psub0 cO cplus cminus copp ceqb lhs0 rhs0) , Strict) ::
         (((psub0 cO cplus cminus copp ceqb rhs0 lhs0) , Strict) :: [])
     | OpNEq -> ((psub0 cO cplus cminus copp ceqb lhs0 rhs0) , Equal) :: []
     | OpLe -> ((psub0 cO cplus cminus copp ceqb lhs0 rhs0) , Strict) :: []
     | OpGe -> ((psub0 cO cplus cminus copp ceqb rhs0 lhs0) , Strict) :: []
     | OpLt -> ((psub0 cO cplus cminus copp ceqb lhs0 rhs0) , NonStrict) ::
         []
     | OpGt -> ((psub0 cO cplus cminus copp ceqb rhs0 lhs0) , NonStrict) ::
         [])

(** val cnf_normalise :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 formula -> 'a1
    nFormula cnf **)

let cnf_normalise cO cI cplus ctimes cminus copp ceqb t0 =
  map (fun x -> x :: []) (xnormalise cO cI cplus ctimes cminus copp ceqb t0)

(** val xnegate :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 formula -> 'a1
    nFormula list **)

let xnegate cO cI cplus ctimes cminus copp ceqb t0 =
  let { flhs = lhs; fop = o; frhs = rhs } = t0 in
  let lhs0 = norm cO cI cplus ctimes cminus copp ceqb lhs in
  let rhs0 = norm cO cI cplus ctimes cminus copp ceqb rhs in
  (match o with
     | OpEq -> ((psub0 cO cplus cminus copp ceqb lhs0 rhs0) , Equal) :: []
     | OpNEq -> ((psub0 cO cplus cminus copp ceqb lhs0 rhs0) , Strict) ::
         (((psub0 cO cplus cminus copp ceqb rhs0 lhs0) , Strict) :: [])
     | OpLe -> ((psub0 cO cplus cminus copp ceqb rhs0 lhs0) , NonStrict) ::
         []
     | OpGe -> ((psub0 cO cplus cminus copp ceqb lhs0 rhs0) , NonStrict) ::
         []
     | OpLt -> ((psub0 cO cplus cminus copp ceqb rhs0 lhs0) , Strict) :: []
     | OpGt -> ((psub0 cO cplus cminus copp ceqb lhs0 rhs0) , Strict) :: [])

(** val cnf_negate :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 formula -> 'a1
    nFormula cnf **)

let cnf_negate cO cI cplus ctimes cminus copp ceqb t0 =
  map (fun x -> x :: []) (xnegate cO cI cplus ctimes cminus copp ceqb t0)

(** val xdenorm : positive -> 'a1 pol -> 'a1 pExpr **)

let rec xdenorm jmp = function
  | Pc c -> PEc c
  | Pinj (j, p2) -> xdenorm (pplus j jmp) p2
  | PX (p2, j, q0) -> PEadd ((PEmul ((xdenorm jmp p2), (PEpow ((PEX jmp),
      (Npos j))))), (xdenorm (psucc jmp) q0))

(** val denorm : 'a1 pol -> 'a1 pExpr **)

let denorm p =
  xdenorm XH p

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
                              | PsatzC c -> PsatzMulE ((PsatzC
                                  (ctimes c p2)), x)
                              | PsatzZ -> PsatzZ
                              | _ -> e)
                       | _ ->
                           (match t2 with
                              | PsatzC c ->
                                  if ceqb cI c
                                  then t1
                                  else PsatzMulE (t1, t2)
                              | PsatzZ -> PsatzZ
                              | _ -> e)))
         | PsatzC c ->
             (match t2 with
                | PsatzMulE (x, x0) ->
                    (match x with
                       | PsatzC p2 -> PsatzMulE ((PsatzC (ctimes c p2)), x0)
                       | _ ->
                           (match x0 with
                              | PsatzC p2 -> PsatzMulE ((PsatzC
                                  (ctimes c p2)), x)
                              | _ ->
                                  if ceqb cI c
                                  then t2
                                  else PsatzMulE (t1, t2)))
                | PsatzAdd (y, z0) -> PsatzAdd ((PsatzMulE ((PsatzC c), y)),
                    (PsatzMulE ((PsatzC c), z0)))
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
  zeq_bool (zmult x.qnum (Zpos y.qden)) (zmult y.qnum (Zpos x.qden))

(** val qle_bool : q -> q -> bool **)

let qle_bool x y =
  zle_bool (zmult x.qnum (Zpos y.qden)) (zmult y.qnum (Zpos x.qden))

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (zplus (zmult x.qnum (Zpos y.qden)) (zmult y.qnum (Zpos x.qden)));
    qden = (pmult x.qden y.qden) }

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (zmult x.qnum y.qnum); qden = (pmult x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (zopp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

(** val pgcdn : nat -> positive -> positive -> positive **)

let rec pgcdn n0 a b =
  match n0 with
    | O -> XH
    | S n1 ->
        (match a with
           | XI a' ->
               (match b with
                  | XI b' ->
                      (match pcompare a' b' Eq with
                         | Eq -> a
                         | Lt -> pgcdn n1 (pminus b' a') a
                         | Gt -> pgcdn n1 (pminus a' b') b)
                  | XO b0 -> pgcdn n1 a b0
                  | XH -> XH)
           | XO a0 ->
               (match b with
                  | XI p -> pgcdn n1 a0 b
                  | XO b0 -> XO (pgcdn n1 a0 b0)
                  | XH -> XH)
           | XH -> XH)

(** val pgcd : positive -> positive -> positive **)

let pgcd a b =
  pgcdn (plus (psize a) (psize b)) a b

(** val zgcd : z -> z -> z **)

let zgcd a b =
  match a with
    | Z0 -> zabs b
    | Zpos a0 ->
        (match b with
           | Z0 -> zabs a
           | Zpos b0 -> Zpos (pgcd a0 b0)
           | Zneg b0 -> Zpos (pgcd a0 b0))
    | Zneg a0 ->
        (match b with
           | Z0 -> zabs a
           | Zpos b0 -> Zpos (pgcd a0 b0)
           | Zneg b0 -> Zpos (pgcd a0 b0))

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

type zWitness = z psatz

(** val zWeakChecker : z nFormula list -> z psatz -> bool **)

let zWeakChecker x x0 =
  check_normalised_formulas Z0 (Zpos XH) zplus zmult zeq_bool zle_bool x x0

(** val psub1 : z pol -> z pol -> z pol **)

let psub1 p p' =
  psub0 Z0 zplus zminus zopp zeq_bool p p'

(** val padd1 : z pol -> z pol -> z pol **)

let padd1 p p' =
  padd0 Z0 zplus zeq_bool p p'

(** val norm0 : z pExpr -> z pol **)

let norm0 pe =
  norm Z0 (Zpos XH) zplus zmult zminus zopp zeq_bool pe

(** val xnormalise0 : z formula -> z nFormula list **)

let xnormalise0 t0 =
  let { flhs = lhs; fop = o; frhs = rhs } = t0 in
  let lhs0 = norm0 lhs in
  let rhs0 = norm0 rhs in
  (match o with
     | OpEq -> ((psub1 lhs0 (padd1 rhs0 (Pc (Zpos XH)))) , NonStrict) ::
         (((psub1 rhs0 (padd1 lhs0 (Pc (Zpos XH)))) , NonStrict) :: [])
     | OpNEq -> ((psub1 lhs0 rhs0) , Equal) :: []
     | OpLe -> ((psub1 lhs0 (padd1 rhs0 (Pc (Zpos XH)))) , NonStrict) :: []
     | OpGe -> ((psub1 rhs0 (padd1 lhs0 (Pc (Zpos XH)))) , NonStrict) :: []
     | OpLt -> ((psub1 lhs0 rhs0) , NonStrict) :: []
     | OpGt -> ((psub1 rhs0 lhs0) , NonStrict) :: [])

(** val normalise : z formula -> z nFormula cnf **)

let normalise t0 =
  map (fun x -> x :: []) (xnormalise0 t0)

(** val xnegate0 : z formula -> z nFormula list **)

let xnegate0 t0 =
  let { flhs = lhs; fop = o; frhs = rhs } = t0 in
  let lhs0 = norm0 lhs in
  let rhs0 = norm0 rhs in
  (match o with
     | OpEq -> ((psub1 lhs0 rhs0) , Equal) :: []
     | OpNEq -> ((psub1 lhs0 (padd1 rhs0 (Pc (Zpos XH)))) , NonStrict) ::
         (((psub1 rhs0 (padd1 lhs0 (Pc (Zpos XH)))) , NonStrict) :: [])
     | OpLe -> ((psub1 rhs0 lhs0) , NonStrict) :: []
     | OpGe -> ((psub1 lhs0 rhs0) , NonStrict) :: []
     | OpLt -> ((psub1 rhs0 (padd1 lhs0 (Pc (Zpos XH)))) , NonStrict) :: []
     | OpGt -> ((psub1 lhs0 (padd1 rhs0 (Pc (Zpos XH)))) , NonStrict) :: [])

(** val negate : z formula -> z nFormula cnf **)

let negate t0 =
  map (fun x -> x :: []) (xnegate0 t0)

(** val ceiling : z -> z -> z **)

let ceiling a b =
  let q0 , r = zdiv_eucl a b in
  (match r with
     | Z0 -> q0
     | _ -> zplus q0 (Zpos XH))

type zArithProof =
  | DoneProof
  | RatProof of zWitness * zArithProof
  | CutProof of zWitness * zArithProof
  | EnumProof of zWitness * zWitness * zArithProof list

(** val isZ0 : z -> bool **)

let isZ0 = function
  | Z0 -> true
  | _ -> false

(** val zgcd_pol : z polC -> z  *  z **)

let rec zgcd_pol = function
  | Pc c -> Z0 , c
  | Pinj (p2, p3) -> zgcd_pol p3
  | PX (p2, p3, q0) ->
      let g1 , c1 = zgcd_pol p2 in
      let g2 , c2 = zgcd_pol q0 in
      if isZ0 g1
      then Z0 , c2
      else if isZ0 (zgcd g1 c1)
           then Z0 , c2
           else if isZ0 g2 then Z0 , c2 else (zgcd (zgcd g1 c1) g2) , c2

(** val zdiv_pol : z polC -> z -> z polC **)

let rec zdiv_pol p x =
  match p with
    | Pc c -> Pc (zdiv c x)
    | Pinj (j, p2) -> Pinj (j, (zdiv_pol p2 x))
    | PX (p2, j, q0) -> PX ((zdiv_pol p2 x), j, (zdiv_pol q0 x))

(** val makeCuttingPlane : z polC -> z polC  *  z **)

let makeCuttingPlane p =
  let g , c = zgcd_pol p in
  if zgt_bool g Z0
  then (zdiv_pol (psubC zminus p c) g) , (zopp (ceiling (zopp c) g))
  else p , Z0

(** val genCuttingPlane : z nFormula -> ((z polC  *  z)  *  op1) option **)

let genCuttingPlane = function
  | e , op ->
      (match op with
         | Equal ->
             let g , c = zgcd_pol e in
             if (&&) (zgt_bool g Z0)
                  ((&&) (zgt_bool c Z0) (negb (zeq_bool (zgcd g c) g)))
             then None
             else Some ((e , Z0) , op)
         | NonEqual -> Some ((e , Z0) , op)
         | Strict ->
             let p , c = makeCuttingPlane (psubC zminus e (Zpos XH)) in
             Some ((p , c) , NonStrict)
         | NonStrict ->
             let p , c = makeCuttingPlane e in Some ((p , c) , NonStrict))

(** val nformula_of_cutting_plane :
    ((z polC  *  z)  *  op1) -> z nFormula **)

let nformula_of_cutting_plane = function
  | e_z , o -> let e , z0 = e_z in (padd1 e (Pc z0)) , o

(** val is_pol_Z0 : z polC -> bool **)

let is_pol_Z0 = function
  | Pc z0 -> (match z0 with
                | Z0 -> true
                | _ -> false)
  | _ -> false

(** val eval_Psatz0 : z nFormula list -> zWitness -> z nFormula option **)

let eval_Psatz0 x x0 =
  eval_Psatz Z0 (Zpos XH) zplus zmult zeq_bool zle_bool x x0

(** val check_inconsistent0 : z nFormula -> bool **)

let check_inconsistent0 f =
  check_inconsistent Z0 zeq_bool zle_bool f

(** val zChecker : z nFormula list -> zArithProof -> bool **)

let rec zChecker l = function
  | DoneProof -> false
  | RatProof (w, pf0) ->
      (match eval_Psatz0 l w with
         | Some f ->
             if check_inconsistent0 f then true else zChecker (f :: l) pf0
         | None -> false)
  | CutProof (w, pf0) ->
      (match eval_Psatz0 l w with
         | Some f ->
             (match genCuttingPlane f with
                | Some cp ->
                    zChecker ((nformula_of_cutting_plane cp) :: l) pf0
                | None -> true)
         | None -> false)
  | EnumProof (w1, w2, pf0) ->
      (match eval_Psatz0 l w1 with
         | Some f1 ->
             (match eval_Psatz0 l w2 with
                | Some f2 ->
                    (match genCuttingPlane f1 with
                       | Some p ->
                           let p2 , op3 = p in
                           let e1 , z1 = p2 in
                           (match genCuttingPlane f2 with
                              | Some p3 ->
                                  let p4 , op4 = p3 in
                                  let e2 , z2 = p4 in
                                  (match op3 with
                                     | NonStrict ->
                                         (match op4 with
                                            | NonStrict ->
                                                if is_pol_Z0 (padd1 e1 e2)
                                                then 
                                                  let rec label pfs lb ub =
                                                    
                                                  match pfs with
                                                    | 
                                                  [] ->
                                                  if z_gt_dec lb ub
                                                  then true
                                                  else false
                                                    | 
                                                  pf1 :: rsr ->
                                                  (&&)
                                                  (zChecker
                                                  (((psub1 e1 (Pc lb)) ,
                                                  Equal) :: l) pf1)
                                                  (label rsr
                                                  (zplus lb (Zpos XH)) ub)
                                                  in label pf0 (zopp z1) z2
                                                else false
                                            | _ -> false)
                                     | _ -> false)
                              | None -> false)
                       | None -> false)
                | None -> false)
         | None -> false)

(** val zTautoChecker : z formula bFormula -> zArithProof list -> bool **)

let zTautoChecker f w =
  tauto_checker normalise negate zChecker f w

(** val n_of_Z : z -> n **)

let n_of_Z = function
  | Zpos p -> Npos p
  | _ -> N0

type qWitness = q psatz

(** val qWeakChecker : q nFormula list -> q psatz -> bool **)

let qWeakChecker x x0 =
  check_normalised_formulas { qnum = Z0; qden = XH } { qnum = (Zpos XH);
    qden = XH } qplus qmult qeq_bool qle_bool x x0

(** val qnormalise : q formula -> q nFormula cnf **)

let qnormalise t0 =
  cnf_normalise { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH }
    qplus qmult qminus qopp qeq_bool t0

(** val qnegate : q formula -> q nFormula cnf **)

let qnegate t0 =
  cnf_negate { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH } qplus
    qmult qminus qopp qeq_bool t0

(** val qTautoChecker : q formula bFormula -> qWitness list -> bool **)

let qTautoChecker f w =
  tauto_checker qnormalise qnegate qWeakChecker f w

type rWitness = z psatz

(** val rWeakChecker : z nFormula list -> z psatz -> bool **)

let rWeakChecker x x0 =
  check_normalised_formulas Z0 (Zpos XH) zplus zmult zeq_bool zle_bool x x0

(** val rnormalise : z formula -> z nFormula cnf **)

let rnormalise t0 =
  cnf_normalise Z0 (Zpos XH) zplus zmult zminus zopp zeq_bool t0

(** val rnegate : z formula -> z nFormula cnf **)

let rnegate t0 =
  cnf_negate Z0 (Zpos XH) zplus zmult zminus zopp zeq_bool t0

(** val rTautoChecker : z formula bFormula -> rWitness list -> bool **)

let rTautoChecker f w =
  tauto_checker rnormalise rnegate rWeakChecker f w

