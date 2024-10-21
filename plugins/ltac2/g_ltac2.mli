(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val test_lpar_idnum_coloneq : unit Procq.Entry.t

val test_lpar_id_colon : unit Procq.Entry.t

val test_lpar_id_coloneq : unit Procq.Entry.t

val test_lpar_id_rpar : unit Procq.Entry.t

val test_ampersand_ident : unit Procq.Entry.t

val test_dollar_ident : unit Procq.Entry.t

val test_ltac1_env : unit Procq.Entry.t

val test_array_opening : unit Procq.Entry.t

val test_array_closing : unit Procq.Entry.t

val test_leftsquarebracket_equal : unit Procq.Entry.t

val _ltac2_expr : Tac2expr.raw_tacexpr Procq.Entry.t

val ltac2_type : Tac2expr.raw_typexpr Procq.Entry.t

val tac2def_val : Tac2expr.strexpr Procq.Entry.t

val tac2def_typ : Tac2expr.strexpr Procq.Entry.t

val tac2def_ext : Tac2expr.strexpr Procq.Entry.t

val tac2def_syn :
  (Tac2expr.sexpr list * int option *
   Tac2expr.raw_tacexpr)
  Procq.Entry.t

val tac2def_mut : Tac2expr.strexpr Procq.Entry.t

val tac2mode : Vernacexpr.vernac_expr Procq.Entry.t

val tac2expr_in_env :
  (Names.Id.t CAst.t list * Tac2expr.raw_tacexpr) Procq.Entry.t

val wit_ltac2_entry : Tac2expr.strexpr Genarg.vernac_genarg_type

val ltac2_entry : Tac2expr.strexpr Procq.Entry.t

val wit_ltac2def_syn :
  (Tac2expr.sexpr list * int option * Tac2expr.raw_tacexpr)
    Genarg.vernac_genarg_type

val ltac2def_syn :
  (Tac2expr.sexpr list * int option *
   Tac2expr.raw_tacexpr)
  Procq.Entry.t

val wit_ltac2_expr : Tac2expr.raw_tacexpr Genarg.vernac_genarg_type

val ltac2_expr : Tac2expr.raw_tacexpr Procq.Entry.t

val ltac2_atom : Tac2expr.raw_tacexpr Procq.Entry.t
