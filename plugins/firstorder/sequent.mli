(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

type t

val has_fuel : t -> bool

val make_simple_atoms : t -> atoms

val iter_redexes : (Formula.any_formula -> unit) -> t -> unit

val deepen: t -> t

val record: Environ.env -> h_item -> t -> t

val lookup: Environ.env -> Evd.evar_map -> h_item -> t -> bool

val add_concl : flags:flags -> Environ.env -> Evd.evar_map -> constr -> t -> t

val add_formula : flags:flags -> hint:bool -> Environ.env -> Evd.evar_map -> GlobRef.t -> constr -> t -> t

val re_add_formula_list : Evd.evar_map -> Formula.any_formula list -> t -> t

val find_left : Evd.evar_map -> atom -> t -> GlobRef.t

val find_goal : Evd.evar_map -> t -> GlobRef.t

val take_formula : Environ.env -> Evd.evar_map -> t -> Formula.any_formula * t

val empty_seq : int -> t

val extend_with_ref_list : flags:flags -> Environ.env -> Evd.evar_map -> GlobRef.t list ->
  t -> t * Evd.evar_map

val extend_with_auto_hints : flags:flags -> Environ.env -> Evd.evar_map -> Hints.hint_db_name list ->
  t -> t * Evd.evar_map

val state : t -> Env.t
