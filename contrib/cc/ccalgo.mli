(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

val init_size : int

type term = 
    Symb of Term.constr 
  | Appli of term * term 

type rule = 
    Congruence 
  | Axiom of Names.identifier      

type valid =
    {lhs : int; 
     rhs : int; 
     rule : rule}

module UF :
sig
  type t 
  val empty : unit -> t
  val add_lst : int -> int -> t -> unit
  val find : t -> int -> int
  val list : t -> int -> int list
  val size : t -> int -> int
  val term : t -> int -> term    
  val subterms : t -> int -> int * int
  val signature : t -> int -> int * int
  val nodes : t -> int list
  val add : term -> t -> int
  val union : t -> int -> int -> valid -> unit
  val join_path : t -> int -> int -> 
    ((int*int)*valid) list*
    ((int*int)*valid) list
end

  
module ST :
sig
  type t
  val empty : unit -> t
  val enter : int -> int * int -> t -> unit
  val query : int * int -> t -> int
  val delete : int -> t -> unit
  val delete_list : int list -> t -> unit
end


val cc : UF.t -> unit

val make_uf :
  (Names.identifier * (term * term)) list -> UF.t

