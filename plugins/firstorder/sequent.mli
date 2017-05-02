(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open EConstr
open Formula
open Globnames

module OrderedConstr: Set.OrderedType with type t=Constr.t

module CM: CSig.MapS with type key=Constr.t

type h_item = global_reference * (int*Constr.t) option

module History: Set.S with type elt = h_item

val cm_add : Evd.evar_map -> constr -> global_reference -> global_reference list CM.t ->
  global_reference list CM.t

val cm_remove : Evd.evar_map -> constr -> global_reference -> global_reference list CM.t ->
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

val lookup: Evd.evar_map -> h_item -> t -> bool

val add_formula : Environ.env -> Evd.evar_map -> side -> global_reference -> constr -> t -> t

val re_add_formula_list : Evd.evar_map -> Formula.t list -> t -> t

val find_left : Evd.evar_map -> constr -> t -> global_reference

val take_formula : Evd.evar_map -> t -> Formula.t * t

val empty_seq : int -> t

val extend_with_ref_list : Environ.env -> Evd.evar_map -> global_reference list ->
  t -> t * Evd.evar_map

val extend_with_auto_hints : Environ.env -> Evd.evar_map -> Hints.hint_db_name list ->
  t -> t * Evd.evar_map

val print_cmap: global_reference list CM.t -> Pp.std_ppcmds
