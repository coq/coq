(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Pattern
open Libnames

(** Named, bounded-depth, term-discrimination nets. *)
module Make :
  functor (Y:Map.OrderedType) ->
sig
  
  module Term_dn : sig     
    type term_label = 
      | GRLabel of global_reference
      | ProdLabel 
      | LambdaLabel
      | SortLabel
  end 
    
  type 'na t
  type 'na frozen_t
    
  val create : unit -> 'na t
    
  val add : 'na t -> ('na * (constr_pattern * Y.t)) -> unit
  val rmv : 'na t -> 'na -> unit
  val in_dn : 'na t -> 'na -> bool
  val remap : 'na t -> 'na -> (constr_pattern * Y.t) -> unit
    
  val lookup : 'na t -> constr -> (constr_pattern * Y.t) list
  val app : ('na -> (constr_pattern * Y.t) -> unit) -> 'na t -> unit
    
  val dnet_depth : int ref
    

  val freeze : 'na t -> 'na frozen_t
  val unfreeze : 'na frozen_t -> 'na t -> unit
  val empty : 'na t -> unit
  val to2lists : 'na t -> ('na * (constr_pattern * Y.t)) list * 
    (Term_dn.term_label option * Btermdn.Make(Y).t) list
end
