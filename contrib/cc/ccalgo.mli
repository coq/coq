(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

type pa_constructor
    (*{head: int; arity: int; args: (int * int) list}*)

module PacMap:Map.S with type key=int * int 

type term = 
    Symb of Term.constr 
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



