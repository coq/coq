(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

type pa_fun=
    {fsym:int;
     fnargs:int}


module PafMap : CSig.MapS with type key = pa_fun
module PacMap : CSig.MapS with type key = pa_constructor

type cinfo =
    {ci_constr: pconstructor; (* inductive type *)
     ci_arity: int;     (* # args *)
     ci_nhyps: int}     (* # projectable args *)

type 'a term

module ATerm :
sig
  type t
  val proj : t -> t term
  val make : t term -> t (* computes and caches constr and hash *)
  val mkSymb : constr -> t
  val mkProduct : (Sorts.t * Sorts.t) -> t
  val mkEps : Id.t -> t
  val mkAppli : (t * t) -> t
  val mkConstructor : cinfo -> t

  val equal : t -> t -> bool (* does not depend on cached values *)
  val constr : t -> constr
  val hash : t -> int
  val nth_arg : t -> int -> t
end

module Constrhash : Hashtbl.S with type key = constr
module Termhash : Hashtbl.S with type key = ATerm.t


type ccpattern =
    PApp of ATerm.t * ccpattern list
  | PVar of int * ccpattern list

type rule=
    Congruence
  | Axiom of constr * bool
  | Injection of int * pa_constructor * int * pa_constructor * int

type from=
    Goal
  | Hyp of constr
  | HeqG of constr
  | HeqnH of constr*constr

type 'a eq = {lhs:int;rhs:int;rule:'a}

type equality = rule eq

type disequality = from eq

type patt_kind =
    Normal
  | Trivial of types
  | Creates_variables

type quant_eq=
    {qe_hyp_id: Id.t;
     qe_pol: bool;
     qe_nvars:int;
     qe_lhs: ccpattern;
     qe_lhs_valid:patt_kind;
     qe_rhs: ccpattern;
     qe_rhs_valid:patt_kind}

type inductive_status =
    Unknown
  | Partial of pa_constructor
  | Partial_applied
  | Total of (int * pa_constructor)

type representative=
    {mutable weight:int;
     mutable lfathers:Int.Set.t;
     mutable fathers:Int.Set.t;
     mutable inductive_status: inductive_status;
     class_type : types;
     mutable functions: Int.Set.t PafMap.t} (*pac -> term = app(constr,t) *)

type cl = Rep of representative| Eqto of int*equality

type vertex = Leaf| Node of (int*int)

type node =
    {mutable clas:cl;
     mutable cpath: int;
     mutable constructors: int PacMap.t;
     vertex:vertex;
     aterm:ATerm.t}

type forest=
    {mutable max_size:int;
     mutable size:int;
     mutable map: node array;
     axioms: (ATerm.t * ATerm.t) Constrhash.t;
     mutable epsilons: pa_constructor list;
     syms: int Termhash.t}

type state

type explanation =
    Discrimination of (int*pa_constructor*int*pa_constructor)
  | Contradiction of disequality
  | Incomplete

type matching_problem

val debug_congruence : CDebug.t

val forest : state -> forest

val axioms : forest -> (ATerm.t * ATerm.t) Constrhash.t

val epsilons : forest -> pa_constructor list

val empty : Environ.env -> Evd.evar_map -> int -> state

val add_aterm : state -> ATerm.t -> int

val add_equality : state -> constr -> ATerm.t -> ATerm.t -> unit

val add_disequality : state -> from -> ATerm.t -> ATerm.t -> unit

val add_quant : state -> Id.t -> bool ->
  int * patt_kind * ccpattern * patt_kind * ccpattern -> unit

val tail_pac : pa_constructor -> pa_constructor

val find : forest -> int -> int

val find_oldest_pac : forest -> int -> pa_constructor -> int

val aterm : forest -> int -> ATerm.t

val get_constructor_info : forest -> int -> cinfo

val subterms : forest -> int -> int * int

val join_path : forest -> int -> int ->
  ((int * int) * equality) list * ((int * int) * equality) list

val execute : bool -> state -> explanation option

val pr_idx_term : Environ.env -> Evd.evar_map -> forest -> int -> Pp.t
