type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

(** val dcompare_inf : comparison -> bool option **)

let dcompare_inf = function
  | Eq -> Some true
  | Lt -> Some false
  | Gt -> None

(** val zcompare_rec :
    z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

let zcompare_rec x y h1 h2 h3 =
  match dcompare_inf (zcompare x y) with
    | Some x0 -> if x0 then h1 __ else h2 __
    | None -> h3 __

(** val z_gt_dec : z -> z -> bool **)

let z_gt_dec x y =
  zcompare_rec x y (fun _ -> false) (fun _ -> false) (fun _ -> true)

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

type 'c pExprC = 'c pExpr

type 'c polC = 'c pol

type op1 =
  | Equal
  | NonEqual
  | Strict
  | NonStrict

type 'c nFormula = 'c pExprC  *  op1

type monoidMember = nat list

type 'c coneMember =
  | S_In of nat
  | S_Ideal of 'c pExprC * 'c coneMember
  | S_Square of 'c pExprC
  | S_Monoid of monoidMember
  | S_Mult of 'c coneMember * 'c coneMember
  | S_Add of 'c coneMember * 'c coneMember
  | S_Pos of 'c
  | S_Z

(** val nformula_times : 'a1 nFormula -> 'a1 nFormula -> 'a1 nFormula **)

let nformula_times f f' =
  let p , op = f in
  let p' , op' = f' in
  (PEmul (p, p')) ,
  (match op with
     | Equal -> Equal
     | NonEqual -> NonEqual
     | Strict -> op'
     | NonStrict -> NonStrict)

(** val nformula_plus : 'a1 nFormula -> 'a1 nFormula -> 'a1 nFormula **)

let nformula_plus f f' =
  let p , op = f in
  let p' , op' = f' in
  (PEadd (p, p')) ,
  (match op with
     | Equal -> op'
     | NonEqual -> NonEqual
     | Strict -> Strict
     | NonStrict -> (match op' with
                       | Strict -> Strict
                       | _ -> NonStrict))

(** val eval_monoid :
    'a1 -> 'a1 nFormula list -> monoidMember -> 'a1 pExprC **)

let rec eval_monoid cI l = function
  | [] -> PEc cI
  | n0 :: ns0 -> PEmul
      ((let q0 , o = nth n0 l ((PEc cI) , NonEqual) in
       (match o with
          | NonEqual -> q0
          | _ -> PEc cI)), (eval_monoid cI l ns0))

(** val eval_cone :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1
    nFormula list -> 'a1 coneMember -> 'a1 nFormula **)

let rec eval_cone cO cI ceqb cleb l = function
  | S_In n0 ->
      let f = nth n0 l ((PEc cO) , Equal) in
      let p , o = f in
      (match o with
         | NonEqual -> (PEc cO) , Equal
         | _ -> f)
  | S_Ideal (p, cm') ->
      let f = eval_cone cO cI ceqb cleb l cm' in
      let q0 , op = f in
      (match op with
         | Equal -> (PEmul (q0, p)) , Equal
         | _ -> f)
  | S_Square p -> (PEmul (p, p)) , NonStrict
  | S_Monoid m -> let p = eval_monoid cI l m in (PEmul (p, p)) , Strict
  | S_Mult (p, q0) ->
      nformula_times (eval_cone cO cI ceqb cleb l p)
        (eval_cone cO cI ceqb cleb l q0)
  | S_Add (p, q0) ->
      nformula_plus (eval_cone cO cI ceqb cleb l p)
        (eval_cone cO cI ceqb cleb l q0)
  | S_Pos c ->
      if (&&) (cleb cO c) (negb (ceqb cO c))
      then (PEc c) , Strict
      else (PEc cO) , Equal
  | S_Z -> (PEc cO) , Equal

(** val normalise_pexpr :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pExprC -> 'a1 polC **)

let normalise_pexpr cO cI cplus ctimes cminus copp ceqb x =
  norm_aux cO cI cplus ctimes cminus copp ceqb x

(** val check_inconsistent :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool)
    -> 'a1 nFormula -> bool **)

let check_inconsistent cO cI cplus ctimes cminus copp ceqb cleb = function
  | e , op ->
      (match normalise_pexpr cO cI cplus ctimes cminus copp ceqb e with
         | Pc c ->
             (match op with
                | Equal -> negb (ceqb c cO)
                | NonEqual -> false
                | Strict -> cleb c cO
                | NonStrict -> (&&) (cleb c cO) (negb (ceqb c cO)))
         | _ -> false)

(** val check_normalised_formulas :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool)
    -> 'a1 nFormula list -> 'a1 coneMember -> bool **)

let check_normalised_formulas cO cI cplus ctimes cminus copp ceqb cleb l cm =
  check_inconsistent cO cI cplus ctimes cminus copp ceqb cleb
    (eval_cone cO cI ceqb cleb l cm)

type op2 =
  | OpEq
  | OpNEq
  | OpLe
  | OpGe
  | OpLt
  | OpGt

type 'c formula = { flhs : 'c pExprC; fop : op2; frhs : 'c pExprC }

(** val flhs : 'a1 formula -> 'a1 pExprC **)

let flhs x = x.flhs

(** val fop : 'a1 formula -> op2 **)

let fop x = x.fop

(** val frhs : 'a1 formula -> 'a1 pExprC **)

let frhs x = x.frhs

(** val xnormalise : 'a1 formula -> 'a1 nFormula list **)

let xnormalise t0 =
  let { flhs = lhs; fop = o; frhs = rhs } = t0 in
  (match o with
     | OpEq -> ((PEsub (lhs, rhs)) , Strict) :: (((PEsub (rhs, lhs)) ,
         Strict) :: [])
     | OpNEq -> ((PEsub (lhs, rhs)) , Equal) :: []
     | OpLe -> ((PEsub (lhs, rhs)) , Strict) :: []
     | OpGe -> ((PEsub (rhs, lhs)) , Strict) :: []
     | OpLt -> ((PEsub (lhs, rhs)) , NonStrict) :: []
     | OpGt -> ((PEsub (rhs, lhs)) , NonStrict) :: [])

(** val cnf_normalise : 'a1 formula -> 'a1 nFormula cnf **)

let cnf_normalise t0 =
  map (fun x -> x :: []) (xnormalise t0)

(** val xnegate : 'a1 formula -> 'a1 nFormula list **)

let xnegate t0 =
  let { flhs = lhs; fop = o; frhs = rhs } = t0 in
  (match o with
     | OpEq -> ((PEsub (lhs, rhs)) , Equal) :: []
     | OpNEq -> ((PEsub (lhs, rhs)) , Strict) :: (((PEsub (rhs, lhs)) ,
         Strict) :: [])
     | OpLe -> ((PEsub (rhs, lhs)) , NonStrict) :: []
     | OpGe -> ((PEsub (lhs, rhs)) , NonStrict) :: []
     | OpLt -> ((PEsub (rhs, lhs)) , Strict) :: []
     | OpGt -> ((PEsub (lhs, rhs)) , Strict) :: [])

(** val cnf_negate : 'a1 formula -> 'a1 nFormula cnf **)

let cnf_negate t0 =
  map (fun x -> x :: []) (xnegate t0)

(** val simpl_expr :
    'a1 -> ('a1 -> 'a1 -> bool) -> 'a1 pExprC -> 'a1 pExprC **)

let rec simpl_expr cI ceqb e = match e with
  | PEadd (x, y) -> PEadd ((simpl_expr cI ceqb x), (simpl_expr cI ceqb y))
  | PEmul (y, z0) ->
      let y' = simpl_expr cI ceqb y in
      (match y' with
         | PEc c ->
             if ceqb c cI
             then simpl_expr cI ceqb z0
             else PEmul (y', (simpl_expr cI ceqb z0))
         | _ -> PEmul (y', (simpl_expr cI ceqb z0)))
  | _ -> e

(** val simpl_cone :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1
    coneMember -> 'a1 coneMember **)

let simpl_cone cO cI ctimes ceqb e = match e with
  | S_Square t0 ->
      let x = simpl_expr cI ceqb t0 in
      (match x with
         | PEc c -> if ceqb cO c then S_Z else S_Pos (ctimes c c)
         | _ -> S_Square x)
  | S_Mult (t1, t2) ->
      (match t1 with
         | S_Mult (x, x0) ->
             (match x with
                | S_Pos p2 ->
                    (match t2 with
                       | S_Pos c -> S_Mult ((S_Pos (ctimes c p2)), x0)
                       | S_Z -> S_Z
                       | _ -> e)
                | _ ->
                    (match x0 with
                       | S_Pos p2 ->
                           (match t2 with
                              | S_Pos c -> S_Mult ((S_Pos (ctimes c p2)), x)
                              | S_Z -> S_Z
                              | _ -> e)
                       | _ ->
                           (match t2 with
                              | S_Pos c ->
                                  if ceqb cI c then t1 else S_Mult (t1, t2)
                              | S_Z -> S_Z
                              | _ -> e)))
         | S_Pos c ->
             (match t2 with
                | S_Mult (x, x0) ->
                    (match x with
                       | S_Pos p2 -> S_Mult ((S_Pos (ctimes c p2)), x0)
                       | _ ->
                           (match x0 with
                              | S_Pos p2 -> S_Mult ((S_Pos (ctimes c p2)), x)
                              | _ ->
                                  if ceqb cI c then t2 else S_Mult (t1, t2)))
                | S_Add (y, z0) -> S_Add ((S_Mult ((S_Pos c), y)), (S_Mult
                    ((S_Pos c), z0)))
                | S_Pos c0 -> S_Pos (ctimes c c0)
                | S_Z -> S_Z
                | _ -> if ceqb cI c then t2 else S_Mult (t1, t2))
         | S_Z -> S_Z
         | _ ->
             (match t2 with
                | S_Pos c -> if ceqb cI c then t1 else S_Mult (t1, t2)
                | S_Z -> S_Z
                | _ -> e))
  | S_Add (t1, t2) ->
      (match t1 with
         | S_Z -> t2
         | _ -> (match t2 with
                   | S_Z -> t1
                   | _ -> S_Add (t1, t2)))
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

type zWitness = z coneMember

(** val zWeakChecker : z nFormula list -> z coneMember -> bool **)

let zWeakChecker x x0 =
  check_normalised_formulas Z0 (Zpos XH) zplus zmult zminus zopp zeq_bool
    zle_bool x x0

(** val xnormalise0 : z formula -> z nFormula list **)

let xnormalise0 t0 =
  let { flhs = lhs; fop = o; frhs = rhs } = t0 in
  (match o with
     | OpEq -> ((PEsub (lhs, (PEadd (rhs, (PEc (Zpos XH)))))) , NonStrict) ::
         (((PEsub (rhs, (PEadd (lhs, (PEc (Zpos XH)))))) , NonStrict) :: [])
     | OpNEq -> ((PEsub (lhs, rhs)) , Equal) :: []
     | OpLe -> ((PEsub (lhs, (PEadd (rhs, (PEc (Zpos XH)))))) , NonStrict) ::
         []
     | OpGe -> ((PEsub (rhs, (PEadd (lhs, (PEc (Zpos XH)))))) , NonStrict) ::
         []
     | OpLt -> ((PEsub (lhs, rhs)) , NonStrict) :: []
     | OpGt -> ((PEsub (rhs, lhs)) , NonStrict) :: [])

(** val normalise : z formula -> z nFormula cnf **)

let normalise t0 =
  map (fun x -> x :: []) (xnormalise0 t0)

(** val xnegate0 : z formula -> z nFormula list **)

let xnegate0 t0 =
  let { flhs = lhs; fop = o; frhs = rhs } = t0 in
  (match o with
     | OpEq -> ((PEsub (lhs, rhs)) , Equal) :: []
     | OpNEq -> ((PEsub (lhs, (PEadd (rhs, (PEc (Zpos XH)))))) , NonStrict)
         :: (((PEsub (rhs, (PEadd (lhs, (PEc (Zpos XH)))))) , NonStrict) ::
         [])
     | OpLe -> ((PEsub (rhs, lhs)) , NonStrict) :: []
     | OpGe -> ((PEsub (lhs, rhs)) , NonStrict) :: []
     | OpLt -> ((PEsub (rhs, (PEadd (lhs, (PEc (Zpos XH)))))) , NonStrict) ::
         []
     | OpGt -> ((PEsub (lhs, (PEadd (rhs, (PEc (Zpos XH)))))) , NonStrict) ::
         [])

(** val negate : z formula -> z nFormula cnf **)

let negate t0 =
  map (fun x -> x :: []) (xnegate0 t0)

(** val ceiling : z -> z -> z **)

let ceiling a b =
  let q0 , r = zdiv_eucl a b in
  (match r with
     | Z0 -> q0
     | _ -> zplus q0 (Zpos XH))

type proofTerm =
  | RatProof of zWitness
  | CutProof of z pExprC * q * zWitness * proofTerm
  | EnumProof of q * z pExprC * q * zWitness * zWitness * proofTerm list

(** val makeLb : z pExpr -> q -> z nFormula **)

let makeLb v q0 =
  let { qnum = n0; qden = d } = q0 in
  (PEsub ((PEmul ((PEc (Zpos d)), v)), (PEc n0))) , NonStrict

(** val qceiling : q -> z **)

let qceiling q0 =
  let { qnum = n0; qden = d } = q0 in ceiling n0 (Zpos d)

(** val makeLbCut : z pExprC -> q -> z nFormula **)

let makeLbCut v q0 =
  (PEsub (v, (PEc (qceiling q0)))) , NonStrict

(** val neg_nformula : z nFormula -> z pExpr  *  op1 **)

let neg_nformula = function
  | e , o -> (PEopp (PEadd (e, (PEc (Zpos XH))))) , o

(** val cutChecker :
    z nFormula list -> z pExpr -> q -> zWitness -> z nFormula option **)

let cutChecker l e lb pf =
  if zWeakChecker ((neg_nformula (makeLb e lb)) :: l) pf
  then Some (makeLbCut e lb)
  else None

(** val zChecker : z nFormula list -> proofTerm -> bool **)

let rec zChecker l = function
  | RatProof pf0 -> zWeakChecker l pf0
  | CutProof (e, q0, pf0, rst) ->
      (match cutChecker l e q0 pf0 with
         | Some c -> zChecker (c :: l) rst
         | None -> false)
  | EnumProof (lb, e, ub, pf1, pf2, rst) ->
      (match cutChecker l e lb pf1 with
         | Some n0 ->
             (match cutChecker l (PEopp e) (qopp ub) pf2 with
                | Some n1 ->
                    let rec label pfs lb0 ub0 =
                      match pfs with
                        | [] -> if z_gt_dec lb0 ub0 then true else false
                        | pf0 :: rsr ->
                            (&&)
                              (zChecker (((PEsub (e, (PEc lb0))) , Equal) ::
                                l) pf0) (label rsr (zplus lb0 (Zpos XH)) ub0)
                    in label rst (qceiling lb) (zopp (qceiling (qopp ub)))
                | None -> false)
         | None -> false)

(** val zTautoChecker : z formula bFormula -> proofTerm list -> bool **)

let zTautoChecker f w =
  tauto_checker normalise negate zChecker f w

(** val map_cone : (nat -> nat) -> zWitness -> zWitness **)

let rec map_cone f e = match e with
  | S_In n0 -> S_In (f n0)
  | S_Ideal (e0, cm) -> S_Ideal (e0, (map_cone f cm))
  | S_Monoid l -> S_Monoid (map f l)
  | S_Mult (cm1, cm2) -> S_Mult ((map_cone f cm1), (map_cone f cm2))
  | S_Add (cm1, cm2) -> S_Add ((map_cone f cm1), (map_cone f cm2))
  | _ -> e

(** val indexes : zWitness -> nat list **)

let rec indexes = function
  | S_In n0 -> n0 :: []
  | S_Ideal (e0, cm) -> indexes cm
  | S_Monoid l -> l
  | S_Mult (cm1, cm2) -> app (indexes cm1) (indexes cm2)
  | S_Add (cm1, cm2) -> app (indexes cm1) (indexes cm2)
  | _ -> []

(** val n_of_Z : z -> n **)

let n_of_Z = function
  | Zpos p -> Npos p
  | _ -> N0

type qWitness = q coneMember

(** val qWeakChecker : q nFormula list -> q coneMember -> bool **)

let qWeakChecker x x0 =
  check_normalised_formulas { qnum = Z0; qden = XH } { qnum = (Zpos XH);
    qden = XH } qplus qmult qminus qopp qeq_bool qle_bool x x0

(** val qTautoChecker : q formula bFormula -> qWitness list -> bool **)

let qTautoChecker f w =
  tauto_checker (fun x -> cnf_normalise x) (fun x -> 
    cnf_negate x) qWeakChecker f w

