(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Formula
open Tacmach
open Globnames

module OrderedConstr: Set.OrderedType with type t=constr

module CM: Map.S with type key=constr

type h_item = global_reference * (int*constr) option

module History: Set.S with type elt = h_item

val cm_add : constr -> global_reference -> global_reference list CM.t ->
  global_reference list CM.t

val cm_remove : constr -> global_reference -> global_reference list CM.t ->
  global_reference list CM.t

module HP: Heap.S with type elt=Formula.t

type t = {redexes:HP.t;
	  context: global_reference list CM.t;
	  latoms:constr list;
	  gl:types;
	  glatom:constr option;
	  cnt:counter;
	  history:History.t;
	  depth:int}

val deepen: t -> t

val record: h_item -> t -> t

val lookup: h_item -> t -> bool

val add_formula : side -> global_reference -> constr -> t ->
  Proof_type.goal sigma -> t

val re_add_formula_list : Formula.t list -> t -> t

val find_left : constr -> t -> global_reference

val take_formula : t -> Formula.t * t

val empty_seq : int -> t

val extend_with_ref_list : global_reference list ->
  t -> Proof_type.goal sigma -> t * Proof_type.goal sigma

val extend_with_auto_hints : Hints.hint_db_name list ->
  t -> Proof_type.goal sigma -> t * Proof_type.goal sigma

val print_cmap: global_reference list CM.t -> Pp.std_ppcmds
