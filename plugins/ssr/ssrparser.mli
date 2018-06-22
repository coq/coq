(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Ltac_plugin

val ssrtacarg : Tacexpr.raw_tactic_expr Pcoq.Entry.t
val wit_ssrtacarg : (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr, Geninterp.Val.t) Genarg.genarg_type
val pr_ssrtacarg : 'a -> 'b -> (Notation_gram.tolerability -> 'c) -> 'c

val ssrtclarg : Tacexpr.raw_tactic_expr Pcoq.Entry.t
val wit_ssrtclarg : (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr, Geninterp.Val.t) Genarg.genarg_type
val pr_ssrtclarg : 'a -> 'b -> (Notation_gram.tolerability -> 'c -> 'd) -> 'c -> 'd

val add_genarg : string -> ('a -> Pp.t) -> 'a Genarg.uniform_genarg_type

(* Parsing witnesses, needed to serialize ssreflect syntax *)
open Ssrmatching_plugin
open Ssrmatching
open Ssrast
open Ssrequality

val wit_ssrrwargs : ssrrwarg list Genarg.uniform_genarg_type
val wit_ssrclauses : clauses Genarg.uniform_genarg_type
val wit_ssrcasearg : (cpattern ssragens) ssrmovearg Genarg.uniform_genarg_type
val wit_ssrmovearg : (cpattern ssragens) ssrmovearg Genarg.uniform_genarg_type
val wit_ssrapplyarg : ssrapplyarg Genarg.uniform_genarg_type
val wit_ssrhavefwdwbinders :
  (Tacexpr.raw_tactic_expr fwdbinders, Tacexpr.glob_tactic_expr fwdbinders, Tacinterp.Value.t fwdbinders) Genarg.genarg_type
