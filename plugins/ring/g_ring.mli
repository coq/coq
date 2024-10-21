(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val wit_ring_mod :
  Constrexpr.constr_expr Ring_ast.ring_mod Genarg.vernac_genarg_type

val ring_mod :
  Constrexpr.constr_expr Ring_ast.ring_mod Procq.Entry.t

val wit_ring_mods :
  Constrexpr.constr_expr Ring_ast.ring_mod list Genarg.vernac_genarg_type

val ring_mods :
  Constrexpr.constr_expr Ring_ast.ring_mod list Procq.Entry.t

val wit_field_mod :
  Constrexpr.constr_expr Ring_ast.field_mod Genarg.vernac_genarg_type

val field_mod :
  Constrexpr.constr_expr Ring_ast.field_mod Procq.Entry.t

val wit_field_mods :
  Constrexpr.constr_expr Ring_ast.field_mod list Genarg.vernac_genarg_type

val field_mods :
  Constrexpr.constr_expr Ring_ast.field_mod list Procq.Entry.t
