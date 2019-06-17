(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Mutils

module Mc = Micromega

val max_nb_cstr : int ref

type var = int

module Monomial : sig
  (** A monomial is represented by a multiset of variables  *)
  type t

   (** [fold f m acc]
       folds over the variables with multiplicities *)
  val fold : (var -> int -> 'a -> 'a) -> t -> 'a -> 'a

  (** [const]
      @return the empty monomial i.e. without any variable *)
  val const : t

  val is_const : t -> bool

  (** [var x]
      @return the monomial x^1 *)
  val var : var -> t

  (** [sqrt m]
      @return [Some r] iff r^2 = m *)
  val sqrt : t -> t option

  (** [is_var m]
      @return [true] iff m = x^1 for some variable x *)
  val is_var : t -> bool

  (** [get_var m]
      @return [x] iff m = x^1 for  variable x *)
  val get_var : t -> var option


  (** [div m1 m2]
      @return a pair [mr,n] such that mr * (m2)^n = m1 where n is maximum *)
  val div : t -> t -> t * int

  (** [compare m1 m2] provides a total order over monomials*)
  val compare : t -> t -> int

  (** [variables m]
      @return the set of variables with (strictly) positive multiplicities *)
  val variables : t -> ISet.t
end

module MonMap : sig
  include Map.S with type key = Monomial.t

  val union : (Monomial.t -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
end

module Poly : sig
  (** Representation of polonomial with rational coefficient.
      a1.m1 + ... + c where
      - ai are rational constants (num type)
      - mi are monomials
      - c is a rational constant

   *)

  type t

  (** [constant c]
      @return the constant polynomial c *)
  val constant : Num.num -> t

  (** [variable x]
      @return the polynomial 1.x^1 *)
  val variable : var -> t

  (** [addition p1 p2]
      @return the polynomial p1+p2 *)
  val addition : t -> t -> t

  (** [product p1 p2]
      @return the polynomial p1*p2 *)
  val product : t -> t -> t

  (** [uminus p]
      @return the polynomial -p i.e product by -1 *)
  val uminus : t -> t

  (** [get mi p]
      @return the coefficient ai of the  monomial mi. *)
  val get : Monomial.t -> t -> Num.num


  (** [fold f p a] folds f over the monomials of p with non-zero coefficient *)
  val fold : (Monomial.t -> Num.num -> 'a -> 'a) -> t -> 'a -> 'a

  (** [add m n p]
      @return the polynomial n*m + p *)
  val add : Monomial.t -> Num.num -> t -> t

end

type cstr = {coeffs : Vect.t ; op : op ; cst : Num.num} (* Representation of linear constraints *)
and op = Eq | Ge | Gt

val eval_op : op -> Num.num -> Num.num -> bool

(*val opMult : op -> op -> op*)

val opAdd  : op -> op -> op

(** [is_strict c]
    @return whether the constraint is strict i.e. c.op = Gt *)
val is_strict : cstr -> bool

exception Strict

module LinPoly : sig
  (** Linear(ised) polynomials represented as a [Vect.t]
      i.e a sorted association list.
      The constant is the coefficient of the variable 0

      Each linear polynomial can be interpreted as a multi-variate polynomial.
      There is a bijection mapping between a linear variable and a monomial
      (see module [MonT])
   *)

  type t = Vect.t

  (** Each variable of a linear polynomial is mapped to a monomial.
      This is done using the monomial tables of the module MonT. *)

  module MonT : sig
    (** [clear ()] clears the mapping. *)
    val clear : unit -> unit

    (** [retrieve x]
        @return the monomial corresponding to the variable [x] *)
    val retrieve : int -> Monomial.t

    (** [register m]
        @return the variable index for the monomial m *)
    val register : Monomial.t -> int

  end

  (** [linpol_of_pol p] linearise the polynomial p *)
  val linpol_of_pol : Poly.t -> t

  (** [var x]
      @return 1.y where y is the variable index of the monomial x^1.
   *)
  val var : var -> t

  (** [coq_poly_of_linpol c p]
      @param p is a multi-variate polynomial.
      @param c maps a rational to a Coq polynomial coefficient.
      @return the coq expression corresponding to polynomial [p].*)
  val coq_poly_of_linpol : (Num.num -> 'a) -> t -> 'a Mc.pExpr

  (** [of_monomial m]
      @returns 1.x where x is the variable (index) for monomial m *)
  val of_monomial : Monomial.t -> t

    (** [of_vect v]
        @returns a1.x1 + ... + an.xn
        This is not the identity because xi is the variable index of xi^1
     *)
  val of_vect : Vect.t -> t

  (** [variables p]
      @return the set of variables of the polynomial p
      interpreted as a multi-variate polynomial *)
  val variables : t -> ISet.t

  (** [is_variable p]
      @return Some x if p = a.x for a >= 0 *)
  val is_variable : t ->  var option

  (** [is_linear p]
      @return whether the multi-variate polynomial is linear. *)
  val is_linear : t -> bool

  (** [is_linear_for x p]
      @return true if the polynomial is linear in x
      i.e can be written c*x+r where c is a constant and r is independent from x *)
  val is_linear_for : var -> t -> bool

  (** [constant c]
      @return the constant polynomial c
   *)
  val constant : Num.num -> t

  (** [search_linear pred p]
      @return a variable x such p = a.x + b such that
      p is linear in x i.e x does not occur in b and
      a is a constant such that [pred a] *)

  val search_linear : (Num.num -> bool) -> t -> var option

  (** [search_all_linear pred p]
      @return all the variables x such p = a.x + b such that
      p is linear in x i.e x does not occur in b and
      a is a constant such that [pred a] *)
  val search_all_linear : (Num.num -> bool) -> t -> var list

 (** [product p q]
     @return the product of the polynomial [p*q] *)
  val product : t -> t -> t

  (** [factorise x p]
      @return [a,b] such that [p = a.x + b]
      and [x] does not occur in [b] *)
  val factorise : var -> t -> t * t

  (** [collect_square p]
      @return a mapping m such that m[s] = s^2
      for every s^2 that is a monomial of [p] *)
  val collect_square : t -> Monomial.t MonMap.t


  (** [pp_var o v] pretty-prints a monomial indexed by v. *)
  val pp_var : out_channel -> var -> unit

  (** [pp o p] pretty-prints a polynomial. *)
  val pp : out_channel -> t -> unit

  (** [pp_goal typ o l] pretty-prints the list of constraints as a Coq goal. *)
  val pp_goal : string -> out_channel -> (t * op) list -> unit

end

module ProofFormat : sig
  (** Proof format used by the proof-generating procedures.
      It is fairly close to Coq format but a bit more liberal.

      It is used for proofs over Z, Q, R.
      However, certain constructions e.g. [CutPrf] are only relevant for Z.
   *)

  type prf_rule =
    | Annot of string * prf_rule
    | Hyp of int
    | Def of int
    | Cst  of Num.num
    | Zero
    | Square of Vect.t
    | MulC of Vect.t * prf_rule
    | Gcd of Big_int.big_int * prf_rule
    | MulPrf of prf_rule * prf_rule
    | AddPrf of prf_rule * prf_rule
    | CutPrf of prf_rule

  type proof =
    | Done
    | Step of int * prf_rule * proof
    | Enum of int * prf_rule * Vect.t * prf_rule * proof list

  val pr_size : prf_rule -> Num.num

  val pr_rule_max_id : prf_rule -> int

  val proof_max_id : proof -> int

  val normalise_proof : int -> proof -> int * proof

  val output_prf_rule : out_channel -> prf_rule -> unit

  val output_proof : out_channel -> proof -> unit

  val add_proof : prf_rule -> prf_rule -> prf_rule

  val mul_cst_proof : Num.num -> prf_rule -> prf_rule

  val mul_proof : prf_rule -> prf_rule -> prf_rule

  val compile_proof : int list -> proof -> Micromega.zArithProof

  val cmpl_prf_rule : ('a Micromega.pExpr -> 'a Micromega.pol) ->
                      (Num.num -> 'a) -> (int list) -> prf_rule -> 'a Micromega.psatz

  val proof_of_farkas : prf_rule IMap.t -> Vect.t -> prf_rule

  val eval_prf_rule : (int -> LinPoly.t * op) -> prf_rule -> LinPoly.t * op

  val eval_proof : (LinPoly.t * op) IMap.t -> proof -> bool

end

val output_cstr : out_channel -> cstr -> unit

val opMult : op -> op -> op

(** [module WithProof] constructs polynomials packed with the proof that their sign is correct. *)
module WithProof :
sig

  type t = (LinPoly.t * op) * ProofFormat.prf_rule

  (** [InvalidProof] is raised if the operation is invalid. *)
  exception InvalidProof

  val annot : string -> t -> t

  val of_cstr : cstr * ProofFormat.prf_rule -> t

  (** [out_channel chan c] pretty-prints the constraint [c] over the channel [chan] *)
  val output : out_channel -> t -> unit

  val output_sys : out_channel -> t list -> unit

  (** [zero] represents the tautology (0=0) *)
  val zero : t

  (** [const n] represents the tautology (n>=0) *)
  val const : Num.num -> t

  (** [product p q]
      @return the polynomial p*q with its sign and proof *)
  val product : t -> t -> t

  (** [addition p q]
      @return the polynomial p+q with its sign and proof *)
  val addition : t -> t -> t

  (** [mult p q]
      @return the polynomial p*q with its sign and proof.
      @raise InvalidProof if p is not a constant and p  is not an equality *)
  val mult : LinPoly.t -> t -> t

  (** [cutting_plane p] does integer reasoning and adjust the constant to be integral *)
  val cutting_plane : t -> t option

  (** [linear_pivot sys p x q]
      @return the polynomial [q] where [x] is eliminated using the polynomial [p]
      The pivoting operation is only defined if
      - p is linear in x i.e p = a.x+b and x neither occurs in a and b
      - The pivoting also requires some sign conditions for [a]
   *)
  val linear_pivot : t list -> t -> Vect.var -> t -> t option


(** [subst sys] performs the equivalent of the 'subst' tactic of Coq.
    For every p=0 \in sys such that p is linear in x with coefficient +/- 1
                               i.e. p = 0 <-> x = e and x \notin e.
    Replace x by e in sys

    NB: performing this transformation may hinders the non-linear prover to find a proof.
    [elim_simple_linear_equality] is much more careful.
 *)

  val subst : t list -> t list

  (** [subst1 sys] performs a single substitution *)
  val subst1 : t list -> t list

  val saturate_subst : bool -> t list -> t list


  val is_substitution : bool -> t -> var option

end
