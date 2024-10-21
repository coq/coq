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

open Ltac_plugin

val ssrtacarg : Tacexpr.raw_tactic_expr Procq.Entry.t
val wit_ssrtacarg : (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr, Geninterp.Val.t) Genarg.genarg_type
val pr_ssrtacarg : Environ.env -> Evd.evar_map -> 'a -> 'b ->
  (Environ.env -> Evd.evar_map -> Constrexpr.entry_relative_level -> 'c) -> 'c

val ssrtclarg : Tacexpr.raw_tactic_expr Procq.Entry.t
val wit_ssrtclarg : (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr, Geninterp.Val.t) Genarg.genarg_type
val pr_ssrtclarg : Environ.env -> Evd.evar_map -> 'a -> 'b ->
  (Environ.env -> Evd.evar_map -> Constrexpr.entry_relative_level -> 'c -> 'd) -> 'c -> 'd

val add_genarg : string -> (Environ.env -> Evd.evar_map -> 'a -> Pp.t) -> 'a Genarg.uniform_genarg_type

(* Parsing witnesses, needed to serialize ssreflect syntax *)
open Ssrmatching_plugin
open Ssrmatching
open Ssrast

type ssrfwdview = ast_closure_term list

val wit_ssrseqarg : (Tacexpr.raw_tactic_expr ssrseqarg, Tacexpr.glob_tactic_expr ssrseqarg, Geninterp.Val.t ssrseqarg) Genarg.genarg_type

val wit_ssrintros_ne : ssripats Genarg.uniform_genarg_type
val wit_ssrintrosarg :
  (Tacexpr.raw_tactic_expr * ssripats,
   Tacexpr.glob_tactic_expr * ssripats,
   Geninterp.Val.t * ssripats) Genarg.genarg_type

val wit_ssripatrep : ssripat Genarg.uniform_genarg_type
val wit_ssrclauses : clauses Genarg.uniform_genarg_type
val wit_ssrhavefwdwbinders :
  (Tacexpr.raw_tactic_expr fwdbinders,
   Tacexpr.glob_tactic_expr fwdbinders,
   Tacinterp.Value.t fwdbinders) Genarg.genarg_type
val wit_ssrhintarg :
  (Tacexpr.raw_tactic_expr ssrhint,
   Tacexpr.glob_tactic_expr ssrhint,
   Tacinterp.Value.t ssrhint) Genarg.genarg_type
val wit_ssrhint3arg :
  (Tacexpr.raw_tactic_expr ssrhint,
   Tacexpr.glob_tactic_expr ssrhint,
   Tacinterp.Value.t ssrhint) Genarg.genarg_type

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

val ssrhpats : ssrhpats Procq.Entry.t
val wit_ssrhpats : ssrhpats Genarg.uniform_genarg_type
val wit_ssrhpats_nobs : ssrhpats Genarg.uniform_genarg_type
val wit_ssrhpats_wtransp : ssrhpats_wtransp Genarg.uniform_genarg_type

val wit_ssrposefwd : (ssrfwdfmt * ast_closure_term) Genarg.uniform_genarg_type

val wit_ssrhavefwd
  : ((ssrfwdfmt * ast_closure_term) * Tacexpr.raw_tactic_expr ssrhint
    , (ssrfwdfmt * ast_closure_term) * Tacexpr.glob_tactic_expr ssrhint
    , (ssrfwdfmt * ast_closure_term) * Geninterp.Val.t ssrhint)
    Genarg.genarg_type

val wit_ssrrpat : ssripat Genarg.uniform_genarg_type
val wit_ssrterm : ssrterm Genarg.uniform_genarg_type

val wit_ssrwgen : clause Genarg.uniform_genarg_type

val wit_ssrfixfwd : (Names.Id.t * (ssrfwdfmt * ast_closure_term)) Genarg.uniform_genarg_type
val wit_ssrfwd : (ssrfwdfmt * ast_closure_term) Genarg.uniform_genarg_type
val wit_ssrfwdfmt : ssrfwdfmt Genarg.uniform_genarg_type

val wit_ssrcofixfwd : (Names.Id.t * (ssrfwdfmt * ast_closure_term)) Genarg.uniform_genarg_type

val wit_ssrcpat : ssripat Genarg.uniform_genarg_type
val wit_ssrdir : ssrdir Genarg.uniform_genarg_type

val wit_ssrclear : (ssrhyps, ssrclear, ssrclear) Genarg.genarg_type

val ssrortacarg : Tacexpr.raw_tactic_expr ssrhint Procq.Entry.t

val ssrhint : Tacexpr.raw_tactic_expr ssrhint Procq.Entry.t
val ssrhintarg : Tacexpr.raw_tactic_expr ssrhint Procq.Entry.t

val ssrmmod : ssrmmod Procq.Entry.t

val ssrclauses : clauses Procq.Entry.t

val ssrintros_ne : ssripats Procq.Entry.t

val ssrorelse : Tacexpr.raw_tactic_expr Procq.Entry.t

val ssrseqarg : Tacexpr.raw_tactic_expr ssrseqarg Procq.Entry.t

val ssrdocc : ssrdocc Procq.Entry.t
val wit_ssrdocc : ssrdocc Genarg.uniform_genarg_type

val ssrocc : ssrocc Procq.Entry.t
val wit_ssrocc : ssrocc Genarg.uniform_genarg_type

val ssrhyp : ssrhyp Procq.Entry.t

type ssripatrep = ssripat

val ssrclear_ne : ssrhyps Procq.Entry.t
val ssrclear : ssrhyps Procq.Entry.t

val ssrintros : ssripats Procq.Entry.t
val wit_ssrintros : ssripats Genarg.uniform_genarg_type

val ssrfwdview : ast_closure_term list Procq.Entry.t
val wit_ssrfwdview : ast_closure_term list Genarg.uniform_genarg_type

val ssrbwdview : ssrterm list Procq.Entry.t
val wit_ssrbwdview : ssrterm list Genarg.uniform_genarg_type

val ssrterm : ssrterm Procq.Entry.t

val ssrsimpl_ne : ssrsimpl Procq.Entry.t

val test_not_ssrslashnum : unit Procq.Entry.t

val ssrmult : ssrmult Procq.Entry.t
val wit_ssrmult : ssrmult Genarg.uniform_genarg_type
val ssrmult_ne : ssrmult Procq.Entry.t

val ssrbinder : (Ssrast.ssrfwdfmt * Constrexpr.constr_expr) Procq.Entry.t

val ast_closure_lterm : ast_closure_term Procq.Entry.t

val ssrwgen : wgen Procq.Entry.t

type ssreqid = ssripat option
type ssrarg = ssrfwdview * (ssreqid * (cpattern ssragens * ssripats))

module Internal : sig
  val register_ssrtac
    : string
    -> Tacenv.ml_tactic
    -> Pptactic.grammar_terminals
    -> Names.KerName.t

  val mk_index : ?loc:Loc.t -> int Locus.or_var -> int Locus.or_var
  val noindex : int Locus.or_var

  val tclintros_expr
    : ?loc:Loc.t
    -> Tacexpr.raw_tactic_expr
    -> ssripats
    -> Tacexpr.raw_tactic_expr

  val intern_ipat
    : Tacintern.glob_sign
    -> Ssrast.ssripat
    -> Ssrast.ssripat

  val interp_ipat
    : Tacinterp.interp_sign
    -> Environ.env
    -> Evd.evar_map
    -> Ssrast.ssripat
    -> Ssrast.ssripat

  val pr_intros : (unit -> Pp.t) -> Ssrast.ssripats -> Pp.t

  val pr_view : ssrterm list -> Pp.t

  val pr_mult : ssrmult -> Pp.t

  val is_ssr_loaded : unit -> bool

  val pr_hpats : ssrhpats -> Pp.t

  val pr_fwd : (Ssrast.ssrfwdkind * Ssrast.ssrbindfmt list) * Ssrast.ast_closure_term -> Pp.t

  val pr_hint :
    'a ->
    'b ->
    ('a -> 'b -> Constrexpr.entry_relative_level -> 'c -> Pp.t) ->
    'c Ssrast.ssrhint -> Pp.t

  val intro_id_to_binder :
    ssripat list ->
    ((ssrfwdkind *
      ssrbindfmt list) *
     Constrexpr.constr_expr)
      list

  val binder_to_intro_id :
    ((ssrfwdkind *
      ssrbindfmt list) *
     Constrexpr.constr_expr)
      list
    -> ssripat list list

  val mkFwdHint : string ->
    ast_closure_term ->
    (ssrfwdkind * ssrbindfmt list) *
    ast_closure_term

  val bind_fwd :
    (('a * 'b list) * Constrexpr.constr_expr) list ->
    ('c * 'b list) * ast_closure_term ->
    ('c * 'b list) * ast_closure_term

  val pr_wgen : wgen -> Pp.t

end

val wit_ast_closure_lterm : ast_closure_term Genarg.uniform_genarg_type

val wit_ast_closure_term : ast_closure_term Genarg.uniform_genarg_type

val wit_ident_no_do  : Names.Id.t Genarg.uniform_genarg_type

val wit_ssrbinder :
  (ssrfwdfmt * Constrexpr.constr_expr,
   ssrfwdfmt * Genintern.glob_constr_and_expr,
   ssrfwdfmt * EConstr.constr) Genarg.genarg_type

val wit_ssrbvar :
  (Constrexpr.constr_expr, Genintern.glob_constr_and_expr, EConstr.constr) Genarg.genarg_type

val wit_ssrclausehyps :
  ((ssrhyps * ((ssrhyp_or_id * string) * cpattern option) option) list,
   (ssrclear * ((ssrhyp_or_id * string) *cpattern option) option) list,
   (ssrclear * ((ssrhyp_or_id * string) * cpattern option) option) list)
    Genarg.genarg_type

val wit_ssrclear_ne : (ssrhyps, ssrclear, ssrclear) Genarg.genarg_type

val wit_ssrhoi_hyp : ssrhyp_or_id Genarg.uniform_genarg_type

val wit_ssrhoi_id : ssrhyp_or_id Genarg.uniform_genarg_type

val wit_ssrhyp : ssrhyp Genarg.uniform_genarg_type

val wit_ssrindex : (int Locus.or_var) Genarg.uniform_genarg_type

val wit_ssriorpat : ssripatss Genarg.uniform_genarg_type

val wit_ssripat : ssripats Genarg.uniform_genarg_type
val wit_ssripats : ssripats Genarg.uniform_genarg_type
val wit_ssripats_ne  : ssripats Genarg.uniform_genarg_type
val wit_ssrmult_ne : (int * ssrmmod) Genarg.uniform_genarg_type
val wit_ssrortacarg :
  (Tacexpr.raw_tactic_expr ssrhint,
   bool * Ltac_plugin.Tacexpr.glob_tactic_expr option list,
   bool * Geninterp.Val.t option list)
    Genarg.genarg_type

val wit_ssrortacs :
  (Tacexpr.raw_tactic_expr option list,
   Tacexpr.glob_tactic_expr option list,
   Geninterp.Val.t option list)
    Genarg.genarg_type

val wit_ssrsimpl_ne :
  ssrsimpl Genarg.uniform_genarg_type

val wit_ssrstruct : Names.Id.t option Genarg.uniform_genarg_type

val wit_ssrtac3arg :
    (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr, Geninterp.Val.t) Genarg.genarg_type
