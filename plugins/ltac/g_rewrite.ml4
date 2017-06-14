(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

(* Syntax for rewriting with strategies *)

open Grammar_API
open Names
open Misctypes
open Locus
open Constrexpr
open Glob_term
open Geninterp
open Extraargs
open Tacmach
open Rewrite
open Stdarg
open Pcoq.Vernac_
open Pcoq.Prim
open Pcoq.Constr
open Pltac

DECLARE PLUGIN "ltac_plugin"

type constr_expr_with_bindings = constr_expr with_bindings
type glob_constr_with_bindings = Tacexpr.glob_constr_and_expr with_bindings
type glob_constr_with_bindings_sign = interp_sign * Tacexpr.glob_constr_and_expr with_bindings

let pr_glob_constr_with_bindings_sign _ _ _ (ge : glob_constr_with_bindings_sign) = Printer.pr_glob_constr (fst (fst (snd ge)))
let pr_glob_constr_with_bindings _ _ _ (ge : glob_constr_with_bindings) = Printer.pr_glob_constr (fst (fst ge))
let pr_constr_expr_with_bindings prc _ _ (ge : constr_expr_with_bindings) = prc (fst ge)
let interp_glob_constr_with_bindings ist gl c = Tacmach.project gl , (ist, c)
let glob_glob_constr_with_bindings ist l = Tacintern.intern_constr_with_bindings ist l
let subst_glob_constr_with_bindings s c =
  Tacsubst.subst_glob_with_bindings s c

ARGUMENT EXTEND glob_constr_with_bindings
    PRINTED BY pr_glob_constr_with_bindings_sign

    INTERPRETED BY interp_glob_constr_with_bindings
    GLOBALIZED BY glob_glob_constr_with_bindings
    SUBSTITUTED BY subst_glob_constr_with_bindings

    RAW_PRINTED BY pr_constr_expr_with_bindings
    GLOB_PRINTED BY pr_glob_constr_with_bindings

   [ constr_with_bindings(bl) ] -> [ bl ]
END

type raw_strategy = (constr_expr, Tacexpr.raw_red_expr) strategy_ast
type glob_strategy = (Tacexpr.glob_constr_and_expr, Tacexpr.raw_red_expr) strategy_ast

let interp_strategy ist gl s = 
  let sigma = project gl in
    sigma, strategy_of_ast s
let glob_strategy ist s = map_strategy (Tacintern.intern_constr ist) (fun c -> c) s
let subst_strategy s str = str

let pr_strategy _ _ _ (s : strategy) = Pp.str "<strategy>"
let pr_raw_strategy prc prlc _ (s : raw_strategy) =
  let prr = Pptactic.pr_red_expr (prc, prlc, Pputils.pr_or_by_notation Libnames.pr_reference, prc) in
  Rewrite.pr_strategy prc prr s
let pr_glob_strategy prc prlc _ (s : glob_strategy) =
  let prr = Pptactic.pr_red_expr
    (Ppconstr.pr_constr_expr,
    Ppconstr.pr_lconstr_expr,
    Pputils.pr_or_by_notation Libnames.pr_reference,
    Ppconstr.pr_constr_expr)
  in
  Rewrite.pr_strategy prc prr s

ARGUMENT EXTEND rewstrategy
    PRINTED BY pr_strategy

    INTERPRETED BY interp_strategy
    GLOBALIZED BY glob_strategy
    SUBSTITUTED BY subst_strategy

    RAW_PRINTED BY pr_raw_strategy
    GLOB_PRINTED BY pr_glob_strategy

    [ glob(c) ] -> [ StratConstr (c, true) ]
  | [ "<-" constr(c) ] -> [ StratConstr (c, false) ]
  | [ "subterms" rewstrategy(h) ] -> [ StratUnary (Subterms, h) ]
  | [ "subterm" rewstrategy(h) ] -> [ StratUnary (Subterm, h) ]
  | [ "innermost" rewstrategy(h) ] -> [ StratUnary(Innermost, h) ]
  | [ "outermost" rewstrategy(h) ] -> [ StratUnary(Outermost, h) ]
  | [ "bottomup" rewstrategy(h) ] -> [ StratUnary(Bottomup, h) ]
  | [ "topdown" rewstrategy(h) ] -> [ StratUnary(Topdown, h) ]
  | [ "id" ] -> [ StratId ]
  | [ "fail" ] -> [ StratFail ]
  | [ "refl" ] -> [ StratRefl ]
  | [ "progress" rewstrategy(h) ] -> [ StratUnary (Progress, h) ]
  | [ "try" rewstrategy(h) ] -> [ StratUnary (Try, h) ]
  | [ "any" rewstrategy(h) ] -> [ StratUnary (Any, h) ]
  | [ "repeat" rewstrategy(h) ] -> [ StratUnary (Repeat, h) ]
  | [ rewstrategy(h) ";" rewstrategy(h') ] -> [ StratBinary (Compose, h, h') ]
  | [ "(" rewstrategy(h) ")" ] -> [ h ]
  | [ "choice" rewstrategy(h) rewstrategy(h') ] -> [ StratBinary (Choice, h, h') ]
  | [ "old_hints" preident(h) ] -> [ StratHints (true, h) ]
  | [ "hints" preident(h) ] -> [ StratHints (false, h) ]
  | [ "terms" constr_list(h) ] -> [ StratTerms h ]
  | [ "eval" red_expr(r) ] -> [ StratEval r ]
  | [ "fold" constr(c) ] -> [ StratFold c ]
END

(* By default the strategy for "rewrite_db" is top-down *)

let db_strat db = StratUnary (Topdown, StratHints (false, db))
let cl_rewrite_clause_db db = cl_rewrite_clause_strat (strategy_of_ast (db_strat db))

TACTIC EXTEND rewrite_strat
| [ "rewrite_strat" rewstrategy(s) "in" hyp(id) ] -> [ cl_rewrite_clause_strat s (Some id) ]
| [ "rewrite_strat" rewstrategy(s) ] -> [ cl_rewrite_clause_strat s None ]
| [ "rewrite_db" preident(db) "in" hyp(id) ] -> [ cl_rewrite_clause_db db (Some id) ]
| [ "rewrite_db" preident(db) ] -> [ cl_rewrite_clause_db db None ]
END

let clsubstitute o c =
  Proofview.Goal.enter begin fun gl ->
  let is_tac id = match fst (fst (snd c)) with { CAst.v = GVar id' } when Id.equal id' id -> true | _ -> false in
  let hyps = Tacmach.New.pf_ids_of_hyps gl in
    Tacticals.New.tclMAP
      (fun cl ->
        match cl with
          | Some id when is_tac id -> Tacticals.New.tclIDTAC
          | _ -> cl_rewrite_clause c o AllOccurrences cl)
      (None :: List.map (fun id -> Some id) hyps)
  end

TACTIC EXTEND substitute
| [ "substitute" orient(o) glob_constr_with_bindings(c) ] -> [ clsubstitute o c ]
END


(* Compatibility with old Setoids *)

TACTIC EXTEND setoid_rewrite
   [ "setoid_rewrite" orient(o) glob_constr_with_bindings(c) ]
   -> [ cl_rewrite_clause c o AllOccurrences None ]
 | [ "setoid_rewrite" orient(o) glob_constr_with_bindings(c) "in" hyp(id) ] ->
      [ cl_rewrite_clause c o AllOccurrences (Some id) ]
 | [ "setoid_rewrite" orient(o) glob_constr_with_bindings(c) "at" occurrences(occ) ] ->
      [ cl_rewrite_clause c o (occurrences_of occ) None ]
 | [ "setoid_rewrite" orient(o) glob_constr_with_bindings(c) "at" occurrences(occ) "in" hyp(id)] ->
      [ cl_rewrite_clause c o (occurrences_of occ) (Some id) ]
 | [ "setoid_rewrite" orient(o) glob_constr_with_bindings(c) "in" hyp(id) "at" occurrences(occ)] ->
      [ cl_rewrite_clause c o (occurrences_of occ) (Some id) ]
END

VERNAC COMMAND EXTEND AddRelation CLASSIFIED AS SIDEFF
  | [ "Add" "Relation" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1)
        "symmetry" "proved" "by" constr(lemma2) "as" ident(n) ] ->
      [ declare_relation a aeq n (Some lemma1) (Some lemma2) None ]

  | [ "Add" "Relation" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1)
        "as" ident(n) ] ->
      [ declare_relation a aeq n (Some lemma1) None None ]
  | [ "Add" "Relation" constr(a) constr(aeq)  "as" ident(n) ] ->
      [ declare_relation a aeq n None None None ]
END

VERNAC COMMAND EXTEND AddRelation2 CLASSIFIED AS SIDEFF
    [ "Add" "Relation" constr(a) constr(aeq) "symmetry" "proved" "by" constr(lemma2)
      "as" ident(n) ] ->
      [ declare_relation a aeq n None (Some lemma2) None ]
  | [ "Add" "Relation" constr(a) constr(aeq) "symmetry" "proved" "by" constr(lemma2) "transitivity" "proved" "by" constr(lemma3)  "as" ident(n) ] ->
      [ declare_relation a aeq n None (Some lemma2) (Some lemma3) ]
END

VERNAC COMMAND EXTEND AddRelation3 CLASSIFIED AS SIDEFF
    [ "Add" "Relation" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1)
      "transitivity" "proved" "by" constr(lemma3) "as" ident(n) ] ->
      [ declare_relation a aeq n (Some lemma1) None (Some lemma3) ]
  | [ "Add" "Relation" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1)
      "symmetry" "proved" "by" constr(lemma2) "transitivity" "proved" "by" constr(lemma3)
      "as" ident(n) ] ->
      [ declare_relation a aeq n (Some lemma1) (Some lemma2) (Some lemma3) ]
  | [ "Add" "Relation" constr(a) constr(aeq) "transitivity" "proved" "by" constr(lemma3)
        "as" ident(n) ] ->
      [ declare_relation a aeq n None None (Some lemma3) ]
END

type binders_argtype = local_binder_expr list

let wit_binders =
 (Genarg.create_arg "binders" : binders_argtype Genarg.uniform_genarg_type)

let binders = Pcoq.create_generic_entry Pcoq.utactic "binders" (Genarg.rawwit wit_binders)

let () =
  let raw_printer _ _ _ l = Pp.pr_non_empty_arg Ppconstr.pr_binders l in
  let printer _ _ _ _ = Pp.str "<Unavailable printer for binders>" in
  Pptactic.declare_extra_genarg_pprule wit_binders raw_printer printer printer

open Pcoq

GEXTEND Gram
  GLOBAL: binders;
    binders:
    [ [ b = Pcoq.Constr.binders -> b ] ];
END

VERNAC COMMAND EXTEND AddParametricRelation CLASSIFIED AS SIDEFF
  | [ "Add" "Parametric" "Relation" binders(b) ":" constr(a) constr(aeq)
        "reflexivity" "proved" "by" constr(lemma1)
        "symmetry" "proved" "by" constr(lemma2) "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n (Some lemma1) (Some lemma2) None ]
  | [ "Add" "Parametric" "Relation" binders(b) ":" constr(a) constr(aeq)
        "reflexivity" "proved" "by" constr(lemma1)
        "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n (Some lemma1) None None ]
  | [ "Add" "Parametric" "Relation" binders(b) ":" constr(a) constr(aeq)  "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n None None None ]
END

VERNAC COMMAND EXTEND AddParametricRelation2 CLASSIFIED AS SIDEFF
    [ "Add" "Parametric" "Relation" binders(b) ":" constr(a) constr(aeq) "symmetry" "proved" "by" constr(lemma2)
      "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n None (Some lemma2) None ]
  | [ "Add" "Parametric" "Relation" binders(b) ":" constr(a) constr(aeq) "symmetry" "proved" "by" constr(lemma2) "transitivity" "proved" "by" constr(lemma3)  "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n None (Some lemma2) (Some lemma3) ]
END

VERNAC COMMAND EXTEND AddParametricRelation3 CLASSIFIED AS SIDEFF
    [ "Add" "Parametric" "Relation" binders(b) ":" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1)
      "transitivity" "proved" "by" constr(lemma3) "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n (Some lemma1) None (Some lemma3) ]
  | [ "Add" "Parametric" "Relation" binders(b) ":" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1)
      "symmetry" "proved" "by" constr(lemma2) "transitivity" "proved" "by" constr(lemma3)
      "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n (Some lemma1) (Some lemma2) (Some lemma3) ]
  | [ "Add" "Parametric" "Relation" binders(b) ":" constr(a) constr(aeq) "transitivity" "proved" "by" constr(lemma3)
        "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n None None (Some lemma3) ]
END

VERNAC COMMAND EXTEND AddSetoid1 CLASSIFIED AS SIDEFF
   [ "Add" "Setoid" constr(a) constr(aeq) constr(t) "as" ident(n) ] ->
     [ add_setoid (not (Locality.make_section_locality (Locality.LocalityFixme.consume ()))) [] a aeq t n ]
  | [ "Add" "Parametric" "Setoid" binders(binders) ":" constr(a) constr(aeq) constr(t) "as" ident(n) ] ->
     [  add_setoid (not (Locality.make_section_locality (Locality.LocalityFixme.consume ()))) binders a aeq t n ]
  | [ "Add" "Morphism" constr(m) ":" ident(n) ]
    (* This command may or may not open a goal *)
    => [ Vernacexpr.VtUnknown, Vernacexpr.VtNow ]
    -> [ add_morphism_infer (not (Locality.make_section_locality (Locality.LocalityFixme.consume ()))) m n ]
  | [ "Add" "Morphism" constr(m) "with" "signature" lconstr(s) "as" ident(n) ]
    => [ Vernacexpr.(VtStartProof("Classic",GuaranteesOpacity,[n]), VtLater) ]
    -> [ add_morphism (not (Locality.make_section_locality (Locality.LocalityFixme.consume ()))) [] m s n ]
  | [ "Add" "Parametric" "Morphism" binders(binders) ":" constr(m)
        "with" "signature" lconstr(s) "as" ident(n) ]
    => [ Vernacexpr.(VtStartProof("Classic",GuaranteesOpacity,[n]), VtLater) ]
    -> [ add_morphism (not (Locality.make_section_locality (Locality.LocalityFixme.consume ()))) binders m s n ]
END

TACTIC EXTEND setoid_symmetry
   [ "setoid_symmetry" ] -> [ setoid_symmetry ]
 | [ "setoid_symmetry" "in" hyp(n) ] -> [ setoid_symmetry_in n ]
END

TACTIC EXTEND setoid_reflexivity
[ "setoid_reflexivity" ] -> [ setoid_reflexivity ]
END

TACTIC EXTEND setoid_transitivity
  [ "setoid_transitivity" constr(t) ] -> [ setoid_transitivity (Some t) ]
| [ "setoid_etransitivity" ] -> [ setoid_transitivity None ]
END

VERNAC COMMAND EXTEND PrintRewriteHintDb CLASSIFIED AS QUERY
  [ "Print" "Rewrite" "HintDb" preident(s) ] -> [ Feedback.msg_notice (Autorewrite.print_rewrite_hintdb s) ]
END
