(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Term
open Util
open Formula
open Tacmach
open Names
open Libnames

val right_reversible : right_pattern -> bool
	
val left_reversible : left_pattern -> bool

module OrderedConstr: Set.OrderedType with type t=constr

module CM: Map.S with type key=constr

module History: Set.S with type elt = global_reference * constr option

val cm_add : constr -> global_reference -> global_reference list CM.t ->
  global_reference list CM.t

val cm_remove : constr -> global_reference -> global_reference list CM.t ->
  global_reference list CM.t

module HP: Heap.S with type elt=left_formula

type t = {redexes:HP.t;
	  context: global_reference list CM.t;
	  latoms:constr list;
	  gl:right_formula;
	  cnt:counter;
	  history:History.t;
	  depth:int}

val deepen: t -> t

val record: global_reference -> constr option -> t -> t

val lookup: global_reference -> constr option -> t -> bool

val add_left : global_reference * constr -> t -> bool -> 
  Proof_type.goal sigma -> t

val re_add_left_list : left_formula list -> t -> t

val change_right : constr -> t -> Proof_type.goal sigma -> t

val find_left : constr -> t -> global_reference

val rev_left : t -> bool

val is_empty_left : t -> bool

val take_left : t -> left_formula * t

val take_right : t -> right_formula

val empty_seq : int -> t

val create_with_ref_list : global_reference list ->
  int -> Proof_type.goal sigma -> t

val create_with_auto_hints : int -> Proof_type.goal sigma -> t

val print_cmap: global_reference list CM.t -> unit 
