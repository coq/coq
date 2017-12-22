(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module implements pretty-printers for vernac_expr syntactic
    objects and their subcomponents. *)

(** Prints a fixpoint body *)
val pr_rec_definition : (Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) -> Pp.t

(** Prints a vernac expression without dot *)
val pr_vernac_expr : Vernacexpr.vernac_expr -> Pp.t

(** Prints a "proof using X" clause. *)
val pr_using : Vernacexpr.section_subset_expr -> Pp.t

(** Prints a vernac expression and closes it with a dot. *)
val pr_vernac : Vernacexpr.vernac_control -> Pp.t
