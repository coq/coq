(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export BinNums.
Require Import BinPos BinNat.

Local Open Scope Z_scope.

Local Notation "0" := Z0.
Local Notation "1" := (Zpos 1).
Local Notation "2" := (Zpos 2).

(***********************************************************)
(** * Binary Integers, Definitions of Operations *)
(***********************************************************)

(** Initial author: Pierre Crégut, CNET, Lannion, France *)

Module Z.

Definition t := Z.

(** ** Nicer names [Z.pos] and [Z.neg] for contructors *)

Notation pos := Zpos.
Notation neg := Zneg.

(** ** Constants *)

Definition zero := 0.
Definition one := 1.
Definition two := 2.

(** ** Doubling and variants *)

Definition double x :=
  match x with
    | 0 => 0
    | pos p => pos p~0
    | neg p => neg p~0
  end.

Definition succ_double x :=
  match x with
    | 0 => 1
    | pos p => pos p~1
    | neg p => neg (Pos.pred_double p)
  end.

Definition pred_double x :=
  match x with
    | 0 => neg 1
    | neg p => neg p~1
    | pos p => pos (Pos.pred_double p)
  end.

(** ** Subtraction of positive into Z *)

Fixpoint pos_sub (x y:positive) {struct y} : Z :=
  match x, y with
    | p~1, q~1 => double (pos_sub p q)
    | p~1, q~0 => succ_double (pos_sub p q)
    | p~1, 1 => pos p~0
    | p~0, q~1 => pred_double (pos_sub p q)
    | p~0, q~0 => double (pos_sub p q)
    | p~0, 1 => pos (Pos.pred_double p)
    | 1, q~1 => neg q~0
    | 1, q~0 => neg (Pos.pred_double q)
    | 1, 1 => Z0
  end%positive.

(** ** Addition *)

Definition add x y :=
  match x, y with
    | 0, y => y
    | x, 0 => x
    | pos x', pos y' => pos (x' + y')
    | pos x', neg y' => pos_sub x' y'
    | neg x', pos y' => pos_sub y' x'
    | neg x', neg y' => neg (x' + y')
  end.

Infix "+" := add : Z_scope.

(** ** Opposite *)

Definition opp x :=
  match x with
    | 0 => 0
    | pos x => neg x
    | neg x => pos x
  end.

Notation "- x" := (opp x) : Z_scope.

(** ** Successor *)

Definition succ x := x + 1.

(** ** Predecessor *)

Definition pred x := x + neg 1.

(** ** Subtraction *)

Definition sub m n := m + -n.

Infix "-" := sub : Z_scope.

(** ** Multiplication *)

Definition mul x y :=
  match x, y with
    | 0, _ => 0
    | _, 0 => 0
    | pos x', pos y' => pos (x' * y')
    | pos x', neg y' => neg (x' * y')
    | neg x', pos y' => neg (x' * y')
    | neg x', neg y' => pos (x' * y')
  end.

Infix "*" := mul : Z_scope.

(** ** Power function *)

Definition pow_pos (z:Z) := Pos.iter (mul z) 1.

Definition pow x y :=
  match y with
    | pos p => pow_pos x p
    | 0 => 1
    | neg _ => 0
  end.

Infix "^" := pow : Z_scope.

(** ** Square *)

Definition square x :=
  match x with
    | 0 => 0
    | pos p => pos (Pos.square p)
    | neg p => pos (Pos.square p)
  end.

(** ** Comparison *)

Definition compare x y :=
  match x, y with
    | 0, 0 => Eq
    | 0, pos y' => Lt
    | 0, neg y' => Gt
    | pos x', 0 => Gt
    | pos x', pos y' => (x' ?= y')%positive
    | pos x', neg y' => Gt
    | neg x', 0 => Lt
    | neg x', pos y' => Lt
    | neg x', neg y' => CompOpp ((x' ?= y')%positive)
  end.

Infix "?=" := compare (at level 70, no associativity) : Z_scope.

(** ** Sign function *)

Definition sgn z :=
  match z with
    | 0 => 0
    | pos p => 1
    | neg p => neg 1
  end.

(** Boolean equality and comparisons *)

Definition leb x y :=
  match x ?= y with
    | Gt => false
    | _ => true
  end.

Definition ltb x y :=
  match x ?= y with
    | Lt => true
    | _ => false
  end.

(** Nota: [geb] and [gtb] are provided for compatibility,
  but [leb] and [ltb] should rather be used instead, since
  more results will be available on them. *)

Definition geb x y :=
  match x ?= y with
    | Lt => false
    | _ => true
  end.

Definition gtb x y :=
  match x ?= y with
    | Gt => true
    | _ => false
  end.

Fixpoint eqb x y :=
  match x, y with
    | 0, 0 => true
    | pos p, pos q => Pos.eqb p q
    | neg p, neg q => Pos.eqb p q
    | _, _ => false
  end.

Infix "=?" := eqb (at level 70, no associativity) : Z_scope.
Infix "<=?" := leb (at level 70, no associativity) : Z_scope.
Infix "<?" := ltb (at level 70, no associativity) : Z_scope.
Infix ">=?" := geb (at level 70, no associativity) : Z_scope.
Infix ">?" := gtb (at level 70, no associativity) : Z_scope.

(** ** Minimum and maximum *)

Definition max n m :=
  match n ?= m with
    | Eq | Gt => n
    | Lt => m
  end.

Definition min n m :=
  match n ?= m with
    | Eq | Lt => n
    | Gt => m
  end.

(** ** Absolute value *)

Definition abs z :=
  match z with
    | 0 => 0
    | pos p => pos p
    | neg p => pos p
  end.

(** ** Conversions *)

(** From [Z] to [nat] via absolute value *)

Definition abs_nat (z:Z) : nat :=
  match z with
    | 0 => 0%nat
    | pos p => Pos.to_nat p
    | neg p => Pos.to_nat p
  end.

(** From [Z] to [N] via absolute value *)

Definition abs_N (z:Z) : N :=
  match z with
    | 0 => 0%N
    | pos p => N.pos p
    | neg p => N.pos p
  end.

(** From [Z] to [nat] by rounding negative numbers to 0 *)

Definition to_nat (z:Z) : nat :=
  match z with
    | pos p => Pos.to_nat p
    | _ => O
  end.

(** From [Z] to [N] by rounding negative numbers to 0 *)

Definition to_N (z:Z) : N :=
  match z with
    | pos p => N.pos p
    | _ => 0%N
  end.

(** From [nat] to [Z] *)

Definition of_nat (n:nat) : Z :=
  match n with
   | O => 0
   | S n => pos (Pos.of_succ_nat n)
  end.

(** From [N] to [Z] *)

Definition of_N (n:N) : Z :=
  match n with
    | 0%N => 0
    | N.pos p => pos p
  end.

(** From [Z] to [positive] by rounding nonpositive numbers to 1 *)

Definition to_pos (z:Z) : positive :=
  match z with
    | pos p => p
    | _ => 1%positive
  end.

(** Conversion with a decimal representation for printing/parsing *)

Definition of_uint (d:Decimal.uint) := of_N (Pos.of_uint d).

Definition of_int (d:Decimal.int) :=
  match d with
  | Decimal.Pos d => of_uint d
  | Decimal.Neg d => opp (of_uint d)
  end.

Definition to_int n :=
  match n with
  | 0 => Decimal.Pos Decimal.zero
  | pos p => Decimal.Pos (Pos.to_uint p)
  | neg p => Decimal.Neg (Pos.to_uint p)
  end.

(** ** Iteration of a function

    By convention, iterating a negative number of times is identity.
*)

Definition iter (n:Z) {A} (f:A -> A) (x:A) :=
  match n with
    | pos p => Pos.iter f x p
    | _ => x
  end.

(** ** Euclidean divisions for binary integers *)

(** Concerning the many possible variants of integer divisions,
    see the headers of the generic files [ZDivFloor], [ZDivTrunc],
    [ZDivEucl], and the article by R. Boute mentioned there.
    We provide here two flavours, Floor and Trunc, while
    the Euclid convention can be found in file Zeuclid.v
    For non-zero b, they all satisfy [a = b*(a/b) + (a mod b)]
    and [ |a mod b| < |b| ], but the sign of the modulo will differ
    when [a<0] and/or [b<0].
*)

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

  In addition, note that we arbitrary take [a/0 = 0] and [a mod 0 = 0].
*)

(** First, a division for positive numbers. Even if the second
   argument is a Z, the answer is arbitrary is it isn't a Zpos. *)

Fixpoint pos_div_eucl (a:positive) (b:Z) : Z * Z :=
  match a with
    | xH => if 2 <=? b then (0, 1) else (1, 0)
    | xO a' =>
      let (q, r) := pos_div_eucl a' b in
      let r' := 2 * r in
      if r' <? b then (2 * q, r') else (2 * q + 1, r' - b)
    | xI a' =>
      let (q, r) := pos_div_eucl a' b in
      let r' := 2 * r + 1 in
      if r' <? b then (2 * q, r') else (2 * q + 1, r' - b)
  end.

(** Then the general euclidean division *)

Definition div_eucl (a b:Z) : Z * Z :=
  match a, b with
    | 0, _ => (0, 0)
    | _, 0 => (0, 0)
    | pos a', pos _ => pos_div_eucl a' b
    | neg a', pos _ =>
      let (q, r) := pos_div_eucl a' b in
	match r with
	  | 0 => (- q, 0)
	  | _ => (- (q + 1), b - r)
	end
    | neg a', neg b' =>
      let (q, r) := pos_div_eucl a' (pos b') in (q, - r)
    | pos a', neg b' =>
      let (q, r) := pos_div_eucl a' (pos b') in
	match r with
	  | 0 => (- q, 0)
	  | _ => (- (q + 1), b + r)
	end
  end.

Definition div (a b:Z) : Z := let (q, _) := div_eucl a b in q.
Definition modulo (a b:Z) : Z := let (_, r) := div_eucl a b in r.

Infix "/" := div : Z_scope.
Infix "mod" := modulo (at level 40, no associativity) : Z_scope.


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

 Note that we arbitrary take here [quot a 0 = 0] and [a rem 0 = a].
*)

Definition quotrem (a b:Z) : Z * Z :=
  match a, b with
   | 0,  _ => (0, 0)
   | _, 0  => (0, a)
   | pos a, pos b =>
     let (q, r) := N.pos_div_eucl a (N.pos b) in (of_N q, of_N r)
   | neg a, pos b =>
     let (q, r) := N.pos_div_eucl a (N.pos b) in (-of_N q, - of_N r)
   | pos a, neg b =>
     let (q, r) := N.pos_div_eucl a (N.pos b) in (-of_N q, of_N r)
   | neg a, neg b =>
     let (q, r) := N.pos_div_eucl a (N.pos b) in (of_N q, - of_N r)
  end.

Definition quot a b := fst (quotrem a b).
Definition rem a b := snd (quotrem a b).

Infix "÷" := quot (at level 40, left associativity) : Z_scope.
(** No infix notation for rem, otherwise it becomes a keyword *)


(** ** Parity functions *)

Definition even z :=
  match z with
    | 0 => true
    | pos (xO _) => true
    | neg (xO _) => true
    | _ => false
  end.

Definition odd z :=
  match z with
    | 0 => false
    | pos (xO _) => false
    | neg (xO _) => false
    | _ => true
  end.


(** ** Division by two *)

(** [div2] performs rounding toward bottom, it is hence a particular
   case of [div], and for all relative number [n] we have:
   [n = 2 * div2 n + if odd n then 1 else 0].  *)

Definition div2 z :=
 match z with
   | 0 => 0
   | pos 1 => 0
   | pos p => pos (Pos.div2 p)
   | neg p => neg (Pos.div2_up p)
 end.

(** [quot2] performs rounding toward zero, it is hence a particular
   case of [quot], and for all relative number [n] we have:
   [n = 2 * quot2 n + if odd n then sgn n else 0].  *)

Definition quot2 (z:Z) :=
  match z with
    | 0 => 0
    | pos 1 => 0
    | pos p => pos (Pos.div2 p)
    | neg 1 => 0
    | neg p => neg (Pos.div2 p)
  end.

(** NB: [Z.quot2] used to be named [Z.div2] in Coq <= 8.3 *)


(** * Base-2 logarithm *)

Definition log2 z :=
  match z with
    | pos (p~1) => pos (Pos.size p)
    | pos (p~0) => pos (Pos.size p)
    | _ => 0
  end.


(** ** Square root *)

Definition sqrtrem n :=
 match n with
  | 0 => (0, 0)
  | pos p =>
    match Pos.sqrtrem p with
     | (s, IsPos r) => (pos s, pos r)
     | (s, _) => (pos s, 0)
    end
  | neg _ => (0,0)
 end.

Definition sqrt n :=
 match n with
  | pos p => pos (Pos.sqrt p)
  | _ => 0
 end.


(** ** Greatest Common Divisor *)

Definition gcd a b :=
  match a,b with
    | 0, _ => abs b
    | _, 0 => abs a
    | pos a, pos b => pos (Pos.gcd a b)
    | pos a, neg b => pos (Pos.gcd a b)
    | neg a, pos b => pos (Pos.gcd a b)
    | neg a, neg b => pos (Pos.gcd a b)
  end.

(** A generalized gcd, also computing division of a and b by gcd. *)

Definition ggcd a b : Z*(Z*Z) :=
  match a,b with
    | 0, _ => (abs b,(0, sgn b))
    | _, 0 => (abs a,(sgn a, 0))
    | pos a, pos b =>
       let '(g,(aa,bb)) := Pos.ggcd a b in (pos g, (pos aa, pos bb))
    | pos a, neg b =>
       let '(g,(aa,bb)) := Pos.ggcd a b in (pos g, (pos aa, neg bb))
    | neg a, pos b =>
       let '(g,(aa,bb)) := Pos.ggcd a b in (pos g, (neg aa, pos bb))
    | neg a, neg b =>
       let '(g,(aa,bb)) := Pos.ggcd a b in (pos g, (neg aa, neg bb))
  end.


(** ** Bitwise functions *)

(** When accessing the bits of negative numbers, all functions
  below will use the two's complement representation. For instance,
  [-1] will correspond to an infinite stream of true bits. If this
  isn't what you're looking for, you can use [abs] first and then
  access the bits of the absolute value.
*)

(** [testbit] : accessing the [n]-th bit of a number [a].
    For negative [n], we arbitrarily answer [false]. *)

Definition testbit a n :=
 match n with
   | 0 => odd a
   | pos p =>
     match a with
       | 0 => false
       | pos a => Pos.testbit a (N.pos p)
       | neg a => negb (N.testbit (Pos.pred_N a) (N.pos p))
     end
   | neg _ => false
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
   | pos p => Pos.iter (mul 2) a p
   | neg p => Pos.iter div2 a p
 end.

Definition shiftr a n := shiftl a (-n).

(** Bitwise operations [lor] [land] [ldiff] [lxor] *)

Definition lor a b :=
 match a, b with
   | 0, _ => b
   | _, 0 => a
   | pos a, pos b => pos (Pos.lor a b)
   | neg a, pos b => neg (N.succ_pos (N.ldiff (Pos.pred_N a) (N.pos b)))
   | pos a, neg b => neg (N.succ_pos (N.ldiff (Pos.pred_N b) (N.pos a)))
   | neg a, neg b => neg (N.succ_pos (N.land (Pos.pred_N a) (Pos.pred_N b)))
 end.

Definition land a b :=
 match a, b with
   | 0, _ => 0
   | _, 0 => 0
   | pos a, pos b => of_N (Pos.land a b)
   | neg a, pos b => of_N (N.ldiff (N.pos b) (Pos.pred_N a))
   | pos a, neg b => of_N (N.ldiff (N.pos a) (Pos.pred_N b))
   | neg a, neg b => neg (N.succ_pos (N.lor (Pos.pred_N a) (Pos.pred_N b)))
 end.

Definition ldiff a b :=
 match a, b with
   | 0, _ => 0
   | _, 0 => a
   | pos a, pos b => of_N (Pos.ldiff a b)
   | neg a, pos b => neg (N.succ_pos (N.lor (Pos.pred_N a) (N.pos b)))
   | pos a, neg b => of_N (N.land (N.pos a) (Pos.pred_N b))
   | neg a, neg b => of_N (N.ldiff (Pos.pred_N b) (Pos.pred_N a))
 end.

Definition lxor a b :=
 match a, b with
   | 0, _ => b
   | _, 0 => a
   | pos a, pos b => of_N (Pos.lxor a b)
   | neg a, pos b => neg (N.succ_pos (N.lxor (Pos.pred_N a) (N.pos b)))
   | pos a, neg b => neg (N.succ_pos (N.lxor (N.pos a) (Pos.pred_N b)))
   | neg a, neg b => of_N (N.lxor (Pos.pred_N a) (Pos.pred_N b))
 end.

Numeral Notation Z of_int to_int : Z_scope.

End Z.

(** Re-export the notation for those who just [Import BinIntDef] *)
Numeral Notation Z Z.of_int Z.to_int : Z_scope.
