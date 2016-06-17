(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module type Pp = sig

  (** Prints a fixpoint body *)
  val pr_rec_definition : (Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) -> Pp.std_ppcmds

  (** Prints a vernac expression *)
  val pr_vernac_body : Vernacexpr.vernac_expr -> Pp.std_ppcmds

  (** Prints a vernac expression and closes it with a dot. *)
  val pr_vernac : Vernacexpr.vernac_expr -> Pp.std_ppcmds

end
