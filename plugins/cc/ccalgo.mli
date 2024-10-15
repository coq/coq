(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Names

type pa_constructor =
    { cnode : int;
      arity : int;
      args  : int list}

type cinfo =
    {ci_constr: pconstructor; (* inductive type *)
     ci_arity: int;     (* # args *)
     ci_nhyps: int}     (* # projectable args *)

type 'a term

module ATerm :
sig
  type t
  val mkSymb : constr -> t
  val mkProduct : (Sorts.t * Sorts.t) -> t
  val mkAppli : (t * t) -> t
  val mkConstructor : Environ.env -> cinfo -> t
  val constr : t -> constr
  val nth_arg : t -> int -> t
end

type ccpattern =
    PApp of ATerm.t * ccpattern list
  | PVar of int * ccpattern list

type axiom

val constr_of_axiom : axiom -> constr

type rule=
    Congruence
  | Axiom of axiom * bool
  | Injection of int * pa_constructor * int * pa_constructor * int

type from=
    Goal
  | Hyp of constr
  | HeqG of Id.t
  | HeqnH of Id.t * Id.t

type 'a eq = {lhs:int;rhs:int;rule:'a}

type equality = rule eq

type disequality = from eq

type patt_kind =
    Normal
  | Trivial of types
  | Creates_variables

type forest

type state

type explanation =
    Discrimination of (int*pa_constructor*int*pa_constructor)
  | Contradiction of disequality
  | Incomplete of (EConstr.t * int) list

val debug_congruence : CDebug.t

val forest : state -> forest

val axioms : forest -> axiom -> ATerm.t * ATerm.t

val empty : Environ.env -> Evd.evar_map -> int -> state

val add_aterm : state -> ATerm.t -> int

val add_equality : state -> Id.t -> ATerm.t -> ATerm.t -> unit

val add_disequality : state -> from -> ATerm.t -> ATerm.t -> unit

val add_quant : state -> Id.t -> bool ->
  int * patt_kind * ccpattern * patt_kind * ccpattern -> unit

val tail_pac : pa_constructor -> pa_constructor

val find_oldest_pac : forest -> int -> pa_constructor -> int

val aterm : forest -> int -> ATerm.t

val get_constructor_info : forest -> int -> cinfo

val subterms : forest -> int -> int * int

val join_path : forest -> int -> int ->
  ((int * int) * equality) list * ((int * int) * equality) list

val execute : bool -> state -> explanation option

val pr_idx_term : Environ.env -> Evd.evar_map -> forest -> int -> Pp.t
