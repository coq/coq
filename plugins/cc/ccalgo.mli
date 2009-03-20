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
  | Product of sorts_family * sorts_family
  | Eps of identifier
  | Appli of term*term
  | Constructor of cinfo (* constructor arity + nhyps *)

type patt_kind =
    Normal 
  | Trivial of types
  | Creates_variables

type ccpattern =
    PApp of term * ccpattern list
  | PVar of int 

type pa_constructor =
    { cnode : int;
      arity : int;
      args  : int list}

module PacMap : Map.S with type key = pa_constructor  

type forest

type state 

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

type explanation =
    Discrimination of (int*pa_constructor*int*pa_constructor)
  | Contradiction of disequality
  | Incomplete

val constr_of_term : term -> constr

val debug : (Pp.std_ppcmds -> unit) -> Pp.std_ppcmds -> unit

val forest : state -> forest

val axioms : forest -> (constr, term * term) Hashtbl.t

val epsilons : forest -> pa_constructor list

val empty : int -> Proof_type.goal Tacmach.sigma -> state

val add_term : state -> term -> int

val add_equality : state -> constr -> term -> term -> unit

val add_disequality : state -> from -> term -> term -> unit

val add_quant : state -> identifier -> bool -> 
  int * patt_kind * ccpattern * patt_kind * ccpattern -> unit

val tail_pac : pa_constructor -> pa_constructor

val find : forest -> int -> int

val find_pac : forest -> int -> pa_constructor -> int

val term : forest -> int -> term

val get_constructor_info : forest -> int -> cinfo

val subterms : forest -> int -> int * int

val join_path : forest -> int -> int -> 
  ((int * int) * equality) list * ((int * int) * equality) list

type quant_eq=
    {qe_hyp_id: identifier;
     qe_pol: bool;
     qe_nvars:int;
     qe_lhs: ccpattern;
     qe_lhs_valid:patt_kind;
     qe_rhs: ccpattern;
     qe_rhs_valid:patt_kind}


type pa_fun=
    {fsym:int;
     fnargs:int}

type matching_problem
 
module PafMap: Map.S with type key = pa_fun

val make_fun_table : state -> Intset.t PafMap.t 

val do_match :  state ->
    (quant_eq * int array) list ref -> matching_problem Stack.t -> unit

val init_pb_stack : state -> matching_problem Stack.t

val paf_of_patt : (term, int) Hashtbl.t -> ccpattern -> pa_fun

val find_instances : state -> (quant_eq * int array) list

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


