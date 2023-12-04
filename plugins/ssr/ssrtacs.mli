
open Ltac_plugin

open Ssrmatching_plugin
open Ssrmatching
open Ssrast
open Ssrequality

open Ssrparser

val wit_ssrarg : ssrarg Genarg.uniform_genarg_type
val wit_ssrrwarg : ssrrwarg Genarg.uniform_genarg_type
val wit_ssrrwargs : ssrrwarg list Genarg.uniform_genarg_type

val wit_ssrseqdir : ssrdir Genarg.uniform_genarg_type

val wit_ssrsufffwd :
  (Tacexpr.raw_tactic_expr ffwbinders,
   Tacexpr.glob_tactic_expr ffwbinders,
   Geninterp.Val.t ffwbinders) Genarg.genarg_type

val wit_ssrcasearg : (cpattern ssragens) ssrmovearg Genarg.uniform_genarg_type
val wit_ssrmovearg : (cpattern ssragens) ssrmovearg Genarg.uniform_genarg_type
val wit_ssrapplyarg : ssrapplyarg Genarg.uniform_genarg_type

val wit_ssrexactarg : ssrapplyarg Genarg.uniform_genarg_type
val wit_ssrcongrarg : ((int * ssrterm) * cpattern ssragens) Genarg.uniform_genarg_type

val wit_ssrunlockarg : (ssrocc * ssrterm) Genarg.uniform_genarg_type
val wit_ssrunlockargs : (ssrocc * ssrterm) list Genarg.uniform_genarg_type

val wit_ssrwlogfwd : (clause list * (ssrfwdfmt * ast_closure_term)) Genarg.uniform_genarg_type

val wit_ssrdgens : cpattern ssragens Genarg.uniform_genarg_type
val wit_ssrdgens_tl : cpattern ssragens Genarg.uniform_genarg_type

val wit_ssr_idcomma : Names.Id.t option option Genarg.uniform_genarg_type

val wit_ssrgen :
    (ssrdocc * cpattern, ssrdocc * cpattern, ssrdocc * cpattern) Genarg.genarg_type

val wit_ssreqid : ssripat option Genarg.uniform_genarg_type

val wit_ssragen :
    (ssrdocc * ssrterm, ssrdocc * ssrterm, ssrdocc * ssrterm) Genarg.genarg_type

val wit_ssragens :
    ((ssrdocc * ssrterm) list list * ssrhyps,
     (ssrdocc * ssrterm) list list * ssrclear,
     (ssrdocc * ssrterm) list list * ssrclear)
      Genarg.genarg_type

val wit_ssrrwocc : ssrdocc Genarg.uniform_genarg_type
val wit_ssrrule_ne : (ssrwkind * ssrterm) Genarg.uniform_genarg_type
val wit_ssrrule : (ssrwkind * ssrterm) Genarg.uniform_genarg_type
val wit_ssrpattern_squarep : (rpattern option) Genarg.uniform_genarg_type
val wit_ssrpattern_ne_squarep : (rpattern option) Genarg.uniform_genarg_type
