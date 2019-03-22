(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
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
val pr_ssrtacarg : Environ.env -> Evd.evar_map -> 'a -> 'b ->
  (Environ.env -> Evd.evar_map -> Notation_gram.tolerability -> 'c) -> 'c

val ssrtclarg : Tacexpr.raw_tactic_expr Pcoq.Entry.t
val wit_ssrtclarg : (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr, Geninterp.Val.t) Genarg.genarg_type
val pr_ssrtclarg : Environ.env -> Evd.evar_map -> 'a -> 'b ->
  (Environ.env -> Evd.evar_map -> Notation_gram.tolerability -> 'c -> 'd) -> 'c -> 'd

val add_genarg : string -> (Environ.env -> Evd.evar_map -> 'a -> Pp.t) -> 'a Genarg.uniform_genarg_type

(* Parsing witnesses, needed to serialize ssreflect syntax *)
open Ssrmatching_plugin
open Ssrmatching
open Ssrast
open Ssrequality

type ssrfwdview = ast_closure_term list
type ssreqid = ssripat option
type ssrarg = ssrfwdview * (ssreqid * (cpattern ssragens * ssripats))

val wit_ssrseqdir : ssrdir Genarg.uniform_genarg_type
val wit_ssrseqarg : (Tacexpr.raw_tactic_expr ssrseqarg, Tacexpr.glob_tactic_expr ssrseqarg, Geninterp.Val.t ssrseqarg) Genarg.genarg_type

val wit_ssrintrosarg :
  (Tacexpr.raw_tactic_expr * ssripats,
   Tacexpr.glob_tactic_expr * ssripats,
   Geninterp.Val.t * ssripats) Genarg.genarg_type

val wit_ssrsufffwd :
  (Tacexpr.raw_tactic_expr ffwbinders,
   Tacexpr.glob_tactic_expr ffwbinders,
   Geninterp.Val.t ffwbinders) Genarg.genarg_type

val wit_ssripatrep : ssripat Genarg.uniform_genarg_type
val wit_ssrarg : ssrarg Genarg.uniform_genarg_type
val wit_ssrrwargs : ssrrwarg list Genarg.uniform_genarg_type
val wit_ssrclauses : clauses Genarg.uniform_genarg_type
val wit_ssrcasearg : (cpattern ssragens) ssrmovearg Genarg.uniform_genarg_type
val wit_ssrmovearg : (cpattern ssragens) ssrmovearg Genarg.uniform_genarg_type
val wit_ssrapplyarg : ssrapplyarg Genarg.uniform_genarg_type
val wit_ssrhavefwdwbinders :
  (Tacexpr.raw_tactic_expr fwdbinders,
   Tacexpr.glob_tactic_expr fwdbinders,
   Tacinterp.Value.t fwdbinders) Genarg.genarg_type
val wit_ssrhintarg :
  (Tacexpr.raw_tactic_expr ssrhint,
   Tacexpr.glob_tactic_expr ssrhint,
   Tacinterp.Value.t ssrhint) Genarg.genarg_type

val wit_ssrexactarg : ssrapplyarg Genarg.uniform_genarg_type
val wit_ssrcongrarg : ((int * ssrterm) * cpattern ssragens) Genarg.uniform_genarg_type
val wit_ssrfwdid : Names.Id.t Genarg.uniform_genarg_type

val wit_ssrsetfwd :
  ((ssrfwdfmt * (cpattern * ast_closure_term option)) * ssrdocc) Genarg.uniform_genarg_type

val wit_ssrdoarg :
  (Tacexpr.raw_tactic_expr ssrdoarg,
   Tacexpr.glob_tactic_expr ssrdoarg,
   Tacinterp.Value.t ssrdoarg) Genarg.genarg_type

val wit_ssrhint :
  (Tacexpr.raw_tactic_expr ssrhint,
   Tacexpr.glob_tactic_expr ssrhint,
   Tacinterp.Value.t ssrhint) Genarg.genarg_type

val wit_ssrhpats : ssrhpats Genarg.uniform_genarg_type
val wit_ssrhpats_nobs : ssrhpats Genarg.uniform_genarg_type
val wit_ssrhpats_wtransp : ssrhpats_wtransp Genarg.uniform_genarg_type

val wit_ssrposefwd : (ssrfwdfmt * ast_closure_term) Genarg.uniform_genarg_type

val wit_ssrrpat : ssripat Genarg.uniform_genarg_type
val wit_ssrterm : ssrterm Genarg.uniform_genarg_type
val wit_ssrunlockarg : (ssrocc * ssrterm) Genarg.uniform_genarg_type
val wit_ssrunlockargs : (ssrocc * ssrterm) list Genarg.uniform_genarg_type

val wit_ssrwgen : clause Genarg.uniform_genarg_type
val wit_ssrwlogfwd : (clause list * (ssrfwdfmt * ast_closure_term)) Genarg.uniform_genarg_type

val wit_ssrfixfwd : (Names.Id.t * (ssrfwdfmt * ast_closure_term)) Genarg.uniform_genarg_type
val wit_ssrfwd : (ssrfwdfmt * ast_closure_term) Genarg.uniform_genarg_type
val wit_ssrfwdfmt : ssrfwdfmt Genarg.uniform_genarg_type

val wit_ssrcpat : ssripat Genarg.uniform_genarg_type
val wit_ssrdgens : cpattern ssragens Genarg.uniform_genarg_type
val wit_ssrdgens_tl : cpattern ssragens Genarg.uniform_genarg_type
val wit_ssrdir : ssrdir Genarg.uniform_genarg_type
