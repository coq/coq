(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


type vname = string;;

type term =
| Zero
| Const of Num.num
| Var of vname
| Inv of term
| Opp of term
| Add of (term * term)
| Sub of (term * term)
| Mul of (term * term)
| Div of (term * term)
| Pow of (term * int)

type positivstellensatz =
   Axiom_eq of int
 | Axiom_le of int
 | Axiom_lt of int
 | Rational_eq of Num.num
 | Rational_le of Num.num
 | Rational_lt of Num.num
 | Square of term
 | Monoid of int list
 | Eqmul of term * positivstellensatz
 | Sum of positivstellensatz * positivstellensatz
 | Product of positivstellensatz * positivstellensatz

type poly

val poly_isconst : poly -> bool

val poly_neg : poly -> poly

val poly_mul : poly -> poly -> poly

val poly_pow : poly -> int -> poly

val poly_const : Num.num -> poly

val poly_of_term : term -> poly

val term_of_poly : poly -> term

val term_of_sos : positivstellensatz * (Num.num * poly) list -> 
     positivstellensatz

val string_of_poly : poly -> string

exception TooDeep

val deepen_until : int -> (int -> 'a) -> int -> 'a

val real_positivnullstellensatz_general : bool -> int -> poly list ->
     (poly * positivstellensatz) list ->
     poly -> poly list * (positivstellensatz * (Num.num * poly) list) list

val sumofsquares : poly -> Num.num * ( Num.num * poly) list
