(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
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

type term =
    Symb of constr
  | Product of Sorts.t * Sorts.t
  | Eps of Id.t
  | Appli of term*term
  | Constructor of cinfo (* constructor arity + nhyps *)

module Constrhash : Hashtbl.S with type key = constr
module Termhash : Hashtbl.S with type key = term


type ccpattern =
    PApp of term * ccpattern list
  | PVar of int

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
     term:term}

type forest=
    {mutable max_size:int;
     mutable size:int;
     mutable map: node array;
     axioms: (term*term) Constrhash.t;
     mutable epsilons: pa_constructor list;
     syms: int Termhash.t}

type state

type explanation =
    Discrimination of (int*pa_constructor*int*pa_constructor)
  | Contradiction of disequality
  | Incomplete

type matching_problem

val term_equal : term -> term -> bool

val constr_of_term : term -> constr

val debug : (unit -> Pp.t) -> unit

val forest : state -> forest

val axioms : forest -> (term * term) Constrhash.t

val epsilons : forest -> pa_constructor list

val empty : int -> Goal.goal Evd.sigma -> state

val add_term : state -> term -> int

val add_equality : state -> constr -> term -> term -> unit

val add_disequality : state -> from -> term -> term -> unit

val add_quant : state -> Id.t -> bool ->
  int * patt_kind * ccpattern * patt_kind * ccpattern -> unit

val tail_pac : pa_constructor -> pa_constructor

val find : forest -> int -> int

val find_pac : forest -> int -> pa_constructor -> int

val find_oldest_pac : forest -> int -> pa_constructor -> int

val term : forest -> int -> term

val get_constructor_info : forest -> int -> cinfo

val subterms : forest -> int -> int * int

val join_path : forest -> int -> int ->
  ((int * int) * equality) list * ((int * int) * equality) list

val make_fun_table : state -> Int.Set.t PafMap.t

val do_match :  state ->
    (quant_eq * int array) list ref -> matching_problem Stack.t -> unit

val init_pb_stack : state -> matching_problem Stack.t

val paf_of_patt : int Termhash.t -> ccpattern -> pa_fun

val find_instances : state -> (quant_eq * int array) list

val execute : bool -> state -> explanation option

val pr_idx_term : forest -> int -> Pp.t

val empty_forest: unit -> forest










(*type pa_constructor


module PacMap:CSig.MapS with type key=pa_constructor

type term =
    Symb of Term.constr
  | Eps
  | Appli of term * term
  | Constructor of Names.constructor*int*int

type rule =
    Congruence
  | Axiom of Names.Id.t
  | Injection of int*int*int*int

type equality =
    {lhs : int;
     rhs : int;
     rule : rule}

module ST :
sig
  type t
  val empty : unit -> t
  val enter : int -> int * int -> t -> unit
  val query : int * int -> t -> int
  val delete : int -> t -> unit
  val delete_list : int list -> t -> unit
end

module UF :
sig
  type t
  exception Discriminable of int * int * int * int * t
  val empty : unit -> t
  val find : t -> int -> int
  val size : t -> int -> int
  val get_constructor : t -> int -> Names.constructor
  val pac_arity : t -> int -> int * int -> int
  val mem_node_pac : t -> int -> int * int -> int
  val add_pacs : t -> int -> pa_constructor PacMap.t ->
    int list * equality list
  val term : t -> int -> term
  val subterms : t -> int -> int * int
  val add : t -> term -> int
  val union : t -> int -> int -> equality -> int list * equality list
  val join_path : t -> int -> int ->
    ((int*int)*equality) list*
    ((int*int)*equality) list
end


val combine_rec : UF.t -> int list -> equality list
val process_rec : UF.t -> equality list -> int list

val cc : UF.t -> unit

val make_uf :
  (Names.Id.t * (term * term)) list -> UF.t

val add_one_diseq : UF.t -> (term * term) -> int * int

val add_disaxioms :
  UF.t -> (Names.Id.t * (term * term)) list ->
  (Names.Id.t * (int * int)) list

val check_equal : UF.t -> int * int -> bool

val find_contradiction : UF.t ->
  (Names.Id.t * (int * int)) list ->
  (Names.Id.t * (int * int))
*)


