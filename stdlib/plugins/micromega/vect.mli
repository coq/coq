(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Num
open Mutils

type var = int
(** Variables are simply (positive) integers. *)

type t
(** The type of vectors or equivalently linear expressions.
           The current implementation is using association lists.
           A list [(0,c),(x1,ai),...,(xn,an)] represents the linear expression
           c + a1.xn + ... an.xn where ai are rational constants and xi are variables.

           Note that the variable 0 has a special meaning and represent a constant.
           Moreover, the representation is spare and variables with a zero coefficient
           are not represented.
        *)

type vector = t

(** {1 Generic functions}  *)

(** [hash] [equal] and [compare] so that Vect.t can be used as
    keys for Set Map and Hashtbl *)

val hash : t -> int
val equal : t -> t -> bool
val compare : t -> t -> int

(** {1 Basic accessors and utility functions} *)

val pp_gen : (out_channel -> var -> unit) -> out_channel -> t -> unit
(** [pp_gen pp_var o v] prints the representation of the vector [v] over the channel [o] *)

val pp : out_channel -> t -> unit
(** [pp o v] prints the representation of the vector [v] over the channel [o] *)

val pp_smt : out_channel -> t -> unit
(** [pp_smt o v] prints the representation of the vector [v] over the channel [o] using SMTLIB conventions *)

val variables : t -> ISet.t
(** [variables v] returns the set of variables with non-zero coefficients *)

val get_cst : t -> num
(** [get_cst v] returns c i.e. the coefficient of the variable zero *)

val decomp_cst : t -> num * t
(** [decomp_cst v] returns the pair (c,a1.x1+...+an.xn) *)

val decomp_at : int -> t -> num * t
(** [decomp_cst v] returns the pair (ai, ai+1.xi+...+an.xn) *)

val decomp_fst : t -> (var * num) * t

val cst : num -> t
(** [cst c] returns the vector v=c+0.x1+...+0.xn *)

val is_constant : t -> bool
(** [is_constant v] holds if [v] is a constant vector i.e. v=c+0.x1+...+0.xn
 *)

val null : t
(** [null] is the empty vector i.e. 0+0.x1+...+0.xn *)

val is_null : t -> bool
(** [is_null v] returns whether [v] is the [null] vector i.e [equal v  null] *)

val get : var -> t -> num
(** [get xi v] returns the coefficient ai of the variable [xi].
    [get] is also defined for the variable 0 *)

val set : var -> num -> t -> t
(** [set xi ai' v] returns the vector c+a1.x1+...ai'.xi+...+an.xn
    i.e. the coefficient of the variable xi is set to ai' *)

val mkvar : var -> t
(** [mkvar xi] returns 1.xi *)

val update : var -> (num -> num) -> t -> t
(** [update xi f v] returns c+a1.x1+...+f(ai).xi+...+an.xn *)

val fresh : t -> int
(** [fresh v] return the fresh variable with index 1+ max (variables v) *)

val choose : t -> (var * num * t) option
(** [choose v] decomposes a vector [v] depending on whether it is [null] or not.
    @return None if v is [null]
    @return Some(x,n,r) where v = r + n.x  x is the smallest variable with non-zero coefficient n <> 0.
 *)

val from_list : num list -> t
(** [from_list l] returns the vector c+a1.x1...an.xn from the list of coefficient [l=c;a1;...;an] *)

val to_list : t -> num list
(** [to_list v] returns the list of all coefficient of the vector v i.e. [c;a1;...;an]
    The list representation is (obviously) not sparsed
    and therefore certain ai may be 0 *)

val decr_var : int -> t -> t
(** [decr_var i v] decrements the variables of the vector [v] by the amount [i].
    Beware, it is only defined if all the variables of v are greater than i
 *)

val incr_var : int -> t -> t
(** [incr_var i v] increments the variables of the vector [v] by the amount [i].
 *)

val gcd : t -> Big_int.big_int
(** [gcd v] returns gcd(num(c),num(a1),...,num(an)) where num extracts
   the numerator of a rational value. *)

val normalise : t -> t
(** [normalise v] returns a vector with only integer coefficients *)

(** {1 Linear arithmetics} *)

val add : t -> t -> t
(** [add v1 v2] is vector addition.
    @param v1 is of the form c +a1.x1  +...+an.xn
    @param v2 is of the form c'+a1'.x1 +...+an'.xn
    @return c1+c1'+ (a1+a1').x1 + ... + (an+an').xn
 *)

val mul : num -> t -> t
(** [mul a v] is vector multiplication of vector [v] by a scalar [a].
    @return a.v = a.c+a.a1.x1+...+a.an.xn *)

val mul_add : num -> t -> num -> t -> t
(** [mul_add c1 v1 c2 v2] returns the linear combination c1.v1+c2.v2 *)

val subst : int -> t -> t -> t
(** [subst x v v'] replaces x by v in vector v' *)

val div : num -> t -> t
(** [div c1 v1] returns the mutiplication by the inverse of c1 i.e (1/c1).v1 *)

val uminus : t -> t
(** [uminus v] @return -v the opposite vector of v i.e. (-1).v  *)

(** {1 Iterators} *)

val fold : ('acc -> var -> num -> 'acc) -> 'acc -> t -> 'acc
(** [fold f acc v] returns f (f (f acc 0 c ) x1 a1 ) ... xn an *)

val fold_error : ('acc -> var -> num -> 'acc option) -> 'acc -> t -> 'acc option
(** [fold_error f acc v] is the same as
    [fold (fun acc x i -> match acc with None -> None | Some acc' -> f acc' x i) (Some acc) v]
    but with early exit...
 *)

val find : (var -> num -> 'c option) -> t -> 'c option
(** [find f v] returns the first [f xi ai] such that [f xi ai <> None].
    If no such xi ai exists, it returns None *)

val for_all : (var -> num -> bool) -> t -> bool
(** [for_all p v] returns /\_{i>=0} (f xi ai) *)

val exists2 : (num -> num -> bool) -> t -> t -> (var * num * num) option
(** [exists2 p v v'] returns Some(xi,ai,ai')
    if p(xi,ai,ai') holds and ai,ai' <> 0.
    It returns None if no such pair of coefficient exists. *)

val dotproduct : t -> t -> num
(** [dotproduct v1 v2] is the dot product of v1 and v2. *)

val map : (var -> num -> 'a) -> t -> 'a list
val abs_min_elt : t -> (var * num) option
val partition : (var -> num -> bool) -> t -> t * t

module Bound : sig
  type t = {cst : num; var : var; coeff : num}
  (** represents a0 + ai.xi  *)

  val of_vect : vector -> t option
end
