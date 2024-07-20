From Stdlib Require Import BinNums PosDef NatDef.

Local Open Scope Z_scope.

Local Notation "0" := Z0.
Local Notation "1" := (Zpos 1).
Local Notation "2" := (Zpos 2).

(***********************************************************)
(** * Binary Integers, Definitions of Operations *)
(***********************************************************)

(** Initial author: Pierre Crégut, CNET, Lannion, France *)

Module Z.

(** ** Doubling and variants *)

Definition double x :=
  match x with
    | 0 => 0
    | Zpos p => Zpos p~0
    | Zneg p => Zneg p~0
  end.

Definition succ_double x :=
  match x with
    | 0 => 1
    | Zpos p => Zpos p~1
    | Zneg p => Zneg (Pos.pred_double p)
  end.

Definition pred_double x :=
  match x with
    | 0 => Zneg 1
    | Zneg p => Zneg p~1
    | Zpos p => Zpos (Pos.pred_double p)
  end.

(** ** Subtraction of positive into Z *)

Fixpoint pos_sub (x y:positive) {struct y} : Z :=
  match x, y with
    | p~1, q~1 => double (pos_sub p q)
    | p~1, q~0 => succ_double (pos_sub p q)
    | p~1, xH => Zpos p~0
    | p~0, q~1 => pred_double (pos_sub p q)
    | p~0, q~0 => double (pos_sub p q)
    | p~0, xH => Zpos (Pos.pred_double p)
    | xH, q~1 => Zneg q~0
    | xH, q~0 => Zneg (Pos.pred_double q)
    | xH, xH => Z0
  end%positive.

(** ** Addition *)

Definition add x y :=
  match x, y with
    | 0, y => y
    | x, 0 => x
    | Zpos x', Zpos y' => Zpos (Pos.add x' y')
    | Zpos x', Zneg y' => pos_sub x' y'
    | Zneg x', Zpos y' => pos_sub y' x'
    | Zneg x', Zneg y' => Zneg (Pos.add x' y')
  end.

Infix "+" := add : Z_scope.

(** ** Opposite *)

Definition opp x :=
  match x with
    | 0 => 0
    | Zpos x => Zneg x
    | Zneg x => Zpos x
  end.

Notation "- x" := (opp x) : Z_scope.

(** ** Subtraction *)

Definition sub m n := m + -n.

Infix "-" := sub : Z_scope.

(** ** Multiplication *)

Definition mul x y :=
  match x, y with
    | 0, _ => 0
    | _, 0 => 0
    | Zpos x', Zpos y' => Zpos (Pos.mul x' y')
    | Zpos x', Zneg y' => Zneg (Pos.mul x' y')
    | Zneg x', Zpos y' => Zneg (Pos.mul x' y')
    | Zneg x', Zneg y' => Zpos (Pos.mul x' y')
  end.

Infix "*" := mul : Z_scope.

(** ** Power function *)

Definition pow_pos (z:Z) := Pos.iter (mul z) 1.

Definition pow x y :=
  match y with
    | Zpos p => pow_pos x p
    | 0 => 1
    | Zneg _ => 0
  end.

Infix "^" := pow : Z_scope.

(** ** Comparison *)

Definition compare x y :=
  match x, y with
    | 0, 0 => Eq
    | 0, Zpos y' => Lt
    | 0, Zneg y' => Gt
    | Zpos x', 0 => Gt
    | Zpos x', Zpos y' => Pos.compare x' y'
    | Zpos x', Zneg y' => Gt
    | Zneg x', 0 => Lt
    | Zneg x', Zpos y' => Lt
    | Zneg x', Zneg y' => CompOpp (Pos.compare x' y')
  end.

Infix "?=" := compare (at level 70, no associativity) : Z_scope.

Definition lt x y := (x ?= y) = Lt.
Definition gt x y := (x ?= y) = Gt.
Definition le x y := (x ?= y) <> Gt.
Definition ge x y := (x ?= y) <> Lt.

Infix "<=" := le : Z_scope.
Infix "<" := lt : Z_scope.
Infix ">=" := ge : Z_scope.
Infix ">" := gt : Z_scope.

(** Boolean equality and comparisons *)

Definition leb x y :=
  match compare x y with
    | Gt => false
    | _ => true
  end.

Definition ltb x y :=
  match compare x y with
    | Lt => true
    | _ => false
  end.

Definition eqb x y :=
  match x, y with
    | 0, 0 => true
    | Zpos p, Zpos q => Pos.eqb p q
    | Zneg p, Zneg q => Pos.eqb p q
    | _, _ => false
  end.

(** ** Minimum and maximum *)

Definition max n m :=
  match compare n m with
    | Eq | Gt => n
    | Lt => m
  end.

Definition min n m :=
  match compare n m with
    | Eq | Lt => n
    | Gt => m
  end.

(** ** Conversions *)

(** From [Z] to [nat] by rounding negative numbers to 0 *)

Definition to_nat (z:Z) : nat :=
  match z with
    | Zpos p => Pos.to_nat p
    | _ => O
  end.

(** From [nat] to [Z] *)

Definition of_nat (n:nat) : Z :=
  match n with
   | O => 0
   | S n => Zpos (Pos.of_succ_nat n)
  end.

(** From [N] to [Z] *)

Definition of_N (n:N) : Z :=
  match n with
    | N0 => 0
    | Npos p => Zpos p
  end.

(** From [Z] to [positive] by rounding nonpositive numbers to 1 *)

Definition to_pos (z:Z) : positive :=
  match z with
    | Zpos p => p
    | _ => 1%positive
  end.

(** ** Euclidean divisions for binary integers *)

(** ** Floor division *)

(** [div_eucl] provides a Truncated-Toward-Bottom (a.k.a Floor)
  Euclidean division. Its projections are named [div] (noted "/")
  and [modulo] (noted with an infix "mod").
  These functions correspond to the `div` and `mod` of Haskell.
  This is the historical convention of Coq.

  The main properties of this convention are :
    - we have [sgn (a mod b) = sgn (b)]
    - [div a b] is the greatest integer smaller or equal to the exact
      fraction [a/b].
    - there is no easy sign rule.

  In addition, note that we take [a/0 = 0] and [a mod 0 = a].
  This choice is motivated by the div-mod equation
    [a = (a / b) * b + (a mod b)] for [b = 0].
*)

(** First, a division for positive numbers. Even if the second
   argument is a Z, the answer is arbitrary if it isn't a Zpos. *)

Fixpoint pos_div_eucl (a:positive) (b:Z) : Z * Z :=
  match a with
    | xH => if leb 2 b then (0, 1) else (1, 0)
    | xO a' =>
      let (q, r) := pos_div_eucl a' b in
      let r' := 2 * r in
      if ltb r' b then (2 * q, r') else (2 * q + 1, r' - b)
    | xI a' =>
      let (q, r) := pos_div_eucl a' b in
      let r' := 2 * r + 1 in
      if ltb r' b then (2 * q, r') else (2 * q + 1, r' - b)
  end.

(** Then the general euclidean division *)

Definition div_eucl (a b:Z) : Z * Z :=
  match a, b with
    | 0, _ => (0, 0)
    | _, 0 => (0, a)
    | Zpos a', Zpos _ => pos_div_eucl a' b
    | Zneg a', Zpos _ =>
      let (q, r) := pos_div_eucl a' b in
        match r with
          | 0 => (- q, 0)
          | _ => (- (q + 1), b - r)
        end
    | Zneg a', Zneg b' =>
      let (q, r) := pos_div_eucl a' (Zpos b') in (q, - r)
    | Zpos a', Zneg b' =>
      let (q, r) := pos_div_eucl a' (Zpos b') in
        match r with
          | 0 => (- q, 0)
          | _ => (- (q + 1), b + r)
        end
  end.

Definition div (a b:Z) : Z := let (q, _) := div_eucl a b in q.
Definition modulo (a b:Z) : Z := let (_, r) := div_eucl a b in r.

(** ** Trunc Division *)

(** [quotrem] provides a Truncated-Toward-Zero Euclidean division.
  Its projections are named [quot] (noted "÷") and [rem].
  These functions correspond to the `quot` and `rem` of Haskell.
  This division convention is used in most programming languages,
  e.g. Ocaml.

  With this convention:
   - we have [sgn(a rem b) = sgn(a)]
   - sign rule for division: [quot (-a) b = quot a (-b) = -(quot a b)]
   - and for modulo: [a rem (-b) = a rem b] and [(-a) rem b = -(a rem b)]

  Note that we take here [quot a 0 = 0] and [a rem 0 = a].
  This choice is motivated by the quot-rem equation
    [a = (quot a b) * b + (a rem b)] for [b = 0].
*)

Definition quotrem (a b:Z) : Z * Z :=
  match a, b with
   | 0,  _ => (0, 0)
   | _, 0  => (0, a)
   | Zpos a, Zpos b =>
     let (q, r) := N.pos_div_eucl a (Npos b) in (of_N q, of_N r)
   | Zneg a, Zpos b =>
     let (q, r) := N.pos_div_eucl a (Npos b) in (-of_N q, - of_N r)
   | Zpos a, Zneg b =>
     let (q, r) := N.pos_div_eucl a (Npos b) in (-of_N q, of_N r)
   | Zneg a, Zneg b =>
     let (q, r) := N.pos_div_eucl a (Npos b) in (of_N q, - of_N r)
  end.

Definition quot a b := fst (quotrem a b).
Definition rem a b := snd (quotrem a b).

Infix "÷" := quot (at level 40, left associativity) : Z_scope.
(** No infix notation for rem, otherwise it becomes a keyword *)

(** ** Parity functions *)

Definition even z :=
  match z with
    | 0 => true
    | Zpos (xO _) => true
    | Zneg (xO _) => true
    | _ => false
  end.

(** ** Division by two *)

(** [div2] performs rounding toward bottom, it is hence a particular
   case of [div], and for all relative number [n] we have:
   [n = 2 * div2 n + if odd n then 1 else 0].  *)

Definition div2 z :=
 match z with
   | 0 => 0
   | Zpos 1 => 0
   | Zpos p => Zpos (Pos.div2 p)
   | Zneg p => Zneg (Pos.div2_up p)
 end.

(** ** Square root *)

Definition sqrtrem n :=
 match n with
  | 0 => (0, 0)
  | Zpos p =>
    match Pos.sqrtrem p with
     | (s, Pos.IsPos r) => (Zpos s, Zpos r)
     | (s, _) => (Zpos s, 0)
    end
  | Zneg _ => (0,0)
 end.

(** Shifts

   Nota: a shift to the right by [-n] will be a shift to the left
   by [n], and vice-versa.

   For fulfilling the two's complement convention, shifting to
   the right a negative number should correspond to a division
   by 2 with rounding toward bottom, hence the use of [div2]
   instead of [quot2].
*)

Definition shiftl a n :=
 match n with
   | 0 => a
   | Zpos p => Pos.iter (mul 2) a p
   | Zneg p => Pos.iter div2 a p
 end.

Definition shiftr a n := shiftl a (-n).

(** Bitwise operations [lor] [land] [ldiff] [lxor] *)

Definition lor a b :=
 match a, b with
   | 0, _ => b
   | _, 0 => a
   | Zpos a, Zpos b => Zpos (Pos.lor a b)
   | Zneg a, Zpos b => Zneg (N.succ_pos (N.ldiff (Pos.pred_N a) (Npos b)))
   | Zpos a, Zneg b => Zneg (N.succ_pos (N.ldiff (Pos.pred_N b) (Npos a)))
   | Zneg a, Zneg b => Zneg (N.succ_pos (N.land (Pos.pred_N a) (Pos.pred_N b)))
 end.

Definition land a b :=
 match a, b with
   | 0, _ => 0
   | _, 0 => 0
   | Zpos a, Zpos b => of_N (Pos.land a b)
   | Zneg a, Zpos b => of_N (N.ldiff (Npos b) (Pos.pred_N a))
   | Zpos a, Zneg b => of_N (N.ldiff (Npos a) (Pos.pred_N b))
   | Zneg a, Zneg b => Zneg (N.succ_pos (N.lor (Pos.pred_N a) (Pos.pred_N b)))
 end.

Definition lxor a b :=
 match a, b with
   | 0, _ => b
   | _, 0 => a
   | Zpos a, Zpos b => of_N (Pos.lxor a b)
   | Zneg a, Zpos b => Zneg (N.succ_pos (N.lxor (Pos.pred_N a) (Npos b)))
   | Zpos a, Zneg b => Zneg (N.succ_pos (N.lxor (Npos a) (Pos.pred_N b)))
   | Zneg a, Zneg b => of_N (N.lxor (Pos.pred_N a) (Pos.pred_N b))
 end.

End Z.
