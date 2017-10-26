(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

val ssrtacarg : Tacexpr.raw_tactic_expr Pcoq.Gram.entry
val wit_ssrtacarg : (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr, Geninterp.Val.t) Genarg.genarg_type
val pr_ssrtacarg : 'a -> 'b -> (Notation_term.tolerability -> 'c) -> 'c

val ssrtclarg : Tacexpr.raw_tactic_expr Pcoq.Gram.entry
val wit_ssrtclarg : (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr, Geninterp.Val.t) Genarg.genarg_type
val pr_ssrtclarg : 'a -> 'b -> (Notation_term.tolerability -> 'c -> 'd) -> 'c -> 'd

val add_genarg : string -> ('a -> Pp.t) -> 'a Genarg.uniform_genarg_type

