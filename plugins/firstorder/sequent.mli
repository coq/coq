(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open EConstr
open Formula

type h_item = GlobRef.t * Unify.Item.t option

type history
type cmap

module HP: Heap.S with type elt=Formula.t

type seqgoal = GoalTerm of EConstr.t | GoalAtom of atom

type t = private {redexes:HP.t;
          context: cmap;
          latoms:atom list;
          gl: seqgoal;
          cnt:counter;
          history:history;
          depth:int}

val deepen: t -> t

val record: h_item -> t -> t

val lookup: Environ.env -> Evd.evar_map -> h_item -> t -> bool

val add_formula : flags:flags -> Environ.env -> Evd.evar_map -> side -> identifier -> constr -> t -> t

val re_add_formula_list : Evd.evar_map -> Formula.t list -> t -> t

val find_left : Evd.evar_map -> constr -> t -> GlobRef.t

val take_formula : Evd.evar_map -> t -> Formula.t * t

val empty_seq : int -> t

val extend_with_ref_list : flags:flags -> Environ.env -> Evd.evar_map -> GlobRef.t list ->
  t -> t * Evd.evar_map

val extend_with_auto_hints : flags:flags -> Environ.env -> Evd.evar_map -> Hints.hint_db_name list ->
  t -> t * Evd.evar_map

val print_cmap: cmap -> Pp.t
