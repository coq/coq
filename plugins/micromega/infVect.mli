(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open NumCompat
open Mutils

(** Variables are simply (positive) integers. *)
type var = int

(** The type of vectors or equivalently linear expressions.
           The current implementation is using association lists.
           A list [(0,c),(x1,ai),...,(xn,an)] represents the linear expression
           c + a1.xn + ... an.xn where ai are rational constants and xi are variables.

           Note that the variable 0 has a special meaning and represent a constant.
           Moreover, the representation is spare and variables with a zero coefficient
           are not represented.
        *)
type t

type vector = t

(** {1 Generic functions}  *)

(** [hash] [equal] and [compare] so that Vect.t can be used as
    keys for Set Map and Hashtbl *)

val hash : t -> int
val equal : t -> t -> bool
val compare : t -> t -> int

(** {1 Basic accessors and utility functions} *)

(** [pp_gen pp_var o v] prints the representation of the vector [v] over the channel [o] *)
val pp_gen : (out_channel -> var -> unit) -> out_channel -> t -> unit

(** [pp o v] prints the representation of the vector [v] over the channel [o] *)
val pp : out_channel -> t -> unit

(** [pp_smt o v] prints the representation of the vector [v] over the channel [o] using SMTLIB conventions *)
val pp_smt : out_channel -> t -> unit

(** [variables v] returns the set of variables with non-zero coefficients *)
val variables : t -> ISet.t

(** [get_cst v] returns c i.e. the coefficient of the variable zero *)
val get_cst : t -> Inf.t

(** [decomp_cst v] returns the pair (c,a1.x1+...+an.xn) *)
val decomp_cst : t -> Inf.t * Vect.t

(** [cst c] returns the vector v=c+0.e + 0.x1+...+0.xn *)
val cst : Q.t -> t

(** [of_cst c] returns the vector v=c + 0.x1+...+0.xn *)
val of_cst : Inf.t -> t


(** [of_vect a1.x1+...+an.xn b ] returns the vector v = 0 - b.e + a1.x1+...+an.xn*)
val of_vect : Vect.t -> bool -> t

(** [is_constant v] holds if [v] is a constant vector i.e. v=c+0.x1+...+0.xn
 *)
val is_constant : t -> bool

(** [null] is the empty vector i.e. 0+0.x1+...+0.xn *)
val null : t

(** [is_null v] returns whether [v] is the [null] vector i.e [equal v  null] *)
val is_null : t -> bool

(** [get xi v] returns the coefficient ai of the variable [xi]. *)
val get : var -> t -> Q.t

(** [set xi ai' v] returns the vector c+a1.x1+...ai'.xi+...+an.xn
    i.e. the coefficient of the variable xi is set to ai' *)
val set : var -> Q.t -> t -> t

(** [update xi f v] returns c+a1.x1+...+f(ai).xi+...+an.xn *)
val update : var -> (Q.t -> Q.t) -> t -> t

(** [fresh v] return the fresh variable with index 1+ max (variables v) *)
val fresh : t -> int

(** [gcd v] returns gcd(num(c),num(a1),...,num(an)) where num extracts
   the numerator of a rational value. *)
val gcd : t -> Z.t

(** [normalise v] returns a vector with only integer coefficients *)
val normalise : t -> t

(** {1 Linear arithmetics} *)

(** [add v1 v2] is vector addition.
    @param v1 is of the form c +a1.x1  +...+an.xn
    @param v2 is of the form c'+a1'.x1 +...+an'.xn
    @return c1+c1'+ (a1+a1').x1 + ... + (an+an').xn
 *)
val add : t -> t -> t

(** [mul a v] is vector multiplication of vector [v] by a scalar [a].
    @return a.v = a.c+a.a1.x1+...+a.an.xn *)
val mul : Q.t -> t -> t

(** [mul_add c1 v1 c2 v2] returns the linear combination c1.v1+c2.v2 *)
val mul_add : Q.t -> t -> Q.t -> t -> t

(** [subst x v v'] replaces x by v in vector v' and also returns the coefficient of x in v' *)
val subst : int -> t -> t -> t

(** [uminus v]
    @return -v the opposite vector of v i.e. (-1).v  *)
val uminus : t -> t
