(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module implements pretty-printers for vernac_expr syntactic
    objects and their subcomponents. *)

val string_of_defined_logical_kind : Decls.defined_logical_kind -> string

val string_of_theorem_kind : Decls.theorem_kind -> string

val pr_set_entry_type : ('a -> Pp.t) -> 'a Extend.constr_entry_key_gen -> Pp.t

val pr_syntax_modifier : Vernacexpr.syntax_modifier CAst.t -> Pp.t

(** Prints a fixpoint body *)
val pr_rec_definition : Constrexpr.fixpoint_order_expr option * Vernacexpr.definition_expr -> Pp.t

(** Prints a scheme *)
val pr_onescheme : Names.lident option * Vernacexpr.scheme -> Pp.t

(** Prints a vernac expression without dot *)
val pr_vernac_expr : Vernacexpr.vernac_expr -> Pp.t

(** Prints a "proof using X" clause. *)
val pr_using : Vernacexpr.section_subset_expr -> Pp.t

(** Prints a vernac expression and closes it with a dot. *)
val pr_vernac : Vernacexpr.vernac_control -> Pp.t
