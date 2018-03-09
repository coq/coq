(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constrexpr

(** Topconstr: This whole module is deprecated in favor of Constrexpr_ops  *)
val asymmetric_patterns : bool ref
[@@ocaml.deprecated "use Constrexpr_ops.asymmetric_patterns"]

(** Utilities on constr_expr *)
val split_at_annot : local_binder_expr list -> Misctypes.lident option -> local_binder_expr list * local_binder_expr list
[@@ocaml.deprecated "use Constrexpr_ops.split_at_annot"]

val ntn_loc : ?loc:Loc.t -> constr_notation_substitution -> notation -> (int * int) list
[@@ocaml.deprecated "use Constrexpr_ops.ntn_loc"]
val patntn_loc : ?loc:Loc.t -> cases_pattern_notation_substitution -> notation -> (int * int) list
[@@ocaml.deprecated "use Constrexpr_ops.patntn_loc"]

(** For cases pattern parsing errors *)
val error_invalid_pattern_notation : ?loc:Loc.t -> unit -> 'a
[@@ocaml.deprecated "use Constrexpr_ops.error_invalid_pattern_notation"]

(*************************************************************************)
val replace_vars_constr_expr : Id.t Id.Map.t -> constr_expr -> constr_expr
[@@ocaml.deprecated "use Constrexpr_ops.free_vars_of_constr_expr"]

val free_vars_of_constr_expr : constr_expr -> Id.Set.t
[@@ocaml.deprecated "use Constrexpr_ops.free_vars_of_constr_expr"]

val occur_var_constr_expr : Id.t -> constr_expr -> bool
[@@ocaml.deprecated "use Constrexpr_ops.occur_var_constr_expr"]

(** Specific function for interning "in indtype" syntax of "match" *)
val ids_of_cases_indtype : cases_pattern_expr -> Id.Set.t
[@@ocaml.deprecated "use Constrexpr_ops.ids_of_cases_indtype"]

(** Used in typeclasses *)
val fold_constr_expr_with_binders : (Id.t -> 'a -> 'a) ->
   ('a -> 'b -> constr_expr -> 'b) -> 'a -> 'b -> constr_expr -> 'b
[@@ocaml.deprecated "use Constrexpr_ops.fold_constr_expr_with_binders"]

val map_constr_expr_with_binders :
  (Id.t -> 'a -> 'a) -> ('a -> constr_expr -> constr_expr) ->
      'a -> constr_expr -> constr_expr
[@@ocaml.deprecated "use Constrexpr_ops.map_constr_expr_with_binders"]
