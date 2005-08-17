(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Term
open Names

type cinfo =
    {ci_constr: constructor; (* inductive type *)
     ci_arity: int;     (* # args *)
     ci_nhyps: int}     (* # projectable args *)

type term =
    Symb of constr
  | Eps
  | Appli of term*term
  | Constructor of cinfo (* constructor arity + nhyps *)

type pa_constructor =
    { cnode : int;
      arity : int;
      args  : int list}

module PacMap : Map.S with type key = pa_constructor  

type forest

type state 

type rule=
    Congruence
  | Axiom of identifier * bool 
  | Injection of int * pa_constructor * int * pa_constructor * int

type from=
    Goal
  | Hyp of identifier
  | HeqG of identifier
  | HeqnH of identifier * identifier

type 'a eq = {lhs:int;rhs:int;rule:'a}

type equality = rule eq

type disequality = from eq

type explanation =
    Discrimination of (int*pa_constructor*int*pa_constructor)
  | Contradiction of disequality
  | Incomplete

val debug : (Pp.std_ppcmds -> unit) -> Pp.std_ppcmds -> unit

val forest : state -> forest

val axioms : forest -> (identifier, term * term) Hashtbl.t

val epsilons : forest -> pa_constructor list

val empty : unit -> state

val add_term : state -> term -> int

val add_equality : state -> identifier -> term -> term -> unit

val add_disequality : state -> from -> term -> term -> unit

val tail_pac : pa_constructor -> pa_constructor

val find : forest -> int -> int

val find_pac : forest -> int -> pa_constructor -> int

val term : forest -> int -> term

val get_constructor_info : forest -> int -> cinfo

val subterms : forest -> int -> int * int

val join_path : forest -> int -> int -> 
  ((int * int) * equality) list * ((int * int) * equality) list

val execute : bool -> state -> explanation option













(*type pa_constructor


module PacMap:Map.S with type key=pa_constructor

type term = 
    Symb of Term.constr 
  | Eps
  | Appli of term * term 
  | Constructor of Names.constructor*int*int

type rule = 
    Congruence 
  | Axiom of Names.identifier
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
  (Names.identifier * (term * term)) list -> UF.t

val add_one_diseq : UF.t -> (term * term) -> int * int

val add_disaxioms : 
  UF.t -> (Names.identifier * (term * term)) list -> 
  (Names.identifier * (int * int)) list
  
val check_equal : UF.t -> int * int -> bool

val find_contradiction : UF.t -> 
  (Names.identifier * (int * int)) list -> 
  (Names.identifier * (int * int))
*)


