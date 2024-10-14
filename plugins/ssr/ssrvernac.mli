(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

val wit_ssrhintref :
  (Constrexpr.constr_expr, Genintern.glob_constr_and_expr,
   EConstr.constr)
    Genarg.genarg_type

val wit_ssrviewpos :
    (Ssrview.AdaptorDb.kind option,
     Ssrview.AdaptorDb.kind option,
     Ssrview.AdaptorDb.kind option)
    Genarg.genarg_type

val wit_ssrviewposspc :
  (Ssrview.AdaptorDb.kind option,
   Ssrview.AdaptorDb.kind option,
   Ssrview.AdaptorDb.kind option)
    Genarg.genarg_type
