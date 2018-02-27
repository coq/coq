(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module implements pretty-printers for vernac_expr syntactic
    objects and their subcomponents. *)

val pr_set_entry_type : ('a -> Pp.t) -> 'a Extend.constr_entry_key_gen -> Pp.t

(** Prints a fixpoint body *)
val pr_rec_definition : (Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) -> Pp.t

(** Prints a vernac expression without dot *)
val pr_vernac_expr : Vernacexpr.vernac_expr -> Pp.t

(** Prints a "proof using X" clause. *)
val pr_using : Vernacexpr.section_subset_expr -> Pp.t

(** Prints a vernac expression and closes it with a dot. *)
val pr_vernac : Vernacexpr.vernac_control -> Pp.t
