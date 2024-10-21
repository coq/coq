(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val wit_hintbases :
  (string list option, string list option, string list option)
  Genarg.genarg_type

val hintbases : string list option Procq.Entry.t

val wit_auto_using :
  (Constrexpr.constr_expr list, Genintern.glob_constr_and_expr list,
   Ltac_pretype.closed_glob_constr list)
  Genarg.genarg_type

val auto_using : Constrexpr.constr_expr list Procq.Entry.t

val wit_hints_path :
  Libnames.qualid Hints.hints_path_gen Genarg.vernac_genarg_type

val hints_path : Libnames.qualid Hints.hints_path_gen Procq.Entry.t

val wit_opthints :
  (string list option, string list option, string list option)
  Genarg.genarg_type

val opthints : string list option Procq.Entry.t
