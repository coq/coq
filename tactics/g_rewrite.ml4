(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

(* Syntax for rewriting with strategies *)

open Names
open Misctypes
open Locus
open Constrexpr
open Glob_term
open Geninterp
open Extraargs
open Tacmach
open Tacticals
open Rewrite

DECLARE PLUGIN "g_rewrite"

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

    RAW_TYPED AS constr_expr_with_bindings
    RAW_PRINTED BY pr_constr_expr_with_bindings

    GLOB_TYPED AS glob_constr_with_bindings
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
let pr_raw_strategy _ _ _ (s : raw_strategy) = Pp.str "<strategy>"
let pr_glob_strategy _ _ _ (s : glob_strategy) = Pp.str "<strategy>"

ARGUMENT EXTEND rewstrategy
    PRINTED BY pr_strategy

    INTERPRETED BY interp_strategy
    GLOBALIZED BY glob_strategy
    SUBSTITUTED BY subst_strategy

    RAW_TYPED AS raw_strategy
    RAW_PRINTED BY pr_raw_strategy

    GLOB_TYPED AS glob_strategy
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

let cl_rewrite_clause_db = 
  if Flags.profile then
    let key = Profile.declare_profile "cl_rewrite_clause_db" in
      Profile.profile3 key cl_rewrite_clause_db
  else cl_rewrite_clause_db

TACTIC EXTEND rewrite_strat
| [ "rewrite_strat" rewstrategy(s) "in" hyp(id) ] -> [ Proofview.V82.tactic (cl_rewrite_clause_strat s (Some id)) ]
| [ "rewrite_strat" rewstrategy(s) ] -> [ Proofview.V82.tactic (cl_rewrite_clause_strat s None) ]
| [ "rewrite_db" preident(db) "in" hyp(id) ] -> [ Proofview.V82.tactic (cl_rewrite_clause_db db (Some id)) ]
| [ "rewrite_db" preident(db) ] -> [ Proofview.V82.tactic (cl_rewrite_clause_db db None) ]
END

let clsubstitute o c =
  let is_tac id = match fst (fst (snd c)) with GVar (_, id') when Id.equal id' id -> true | _ -> false in
    Tacticals.onAllHypsAndConcl
      (fun cl ->
        match cl with
          | Some id when is_tac id -> tclIDTAC
          | _ -> cl_rewrite_clause c o AllOccurrences cl)

TACTIC EXTEND substitute
| [ "substitute" orient(o) glob_constr_with_bindings(c) ] -> [ Proofview.V82.tactic (clsubstitute o c) ]
END


(* Compatibility with old Setoids *)

TACTIC EXTEND setoid_rewrite
   [ "setoid_rewrite" orient(o) glob_constr_with_bindings(c) ]
   -> [ Proofview.V82.tactic (cl_rewrite_clause c o AllOccurrences None) ]
 | [ "setoid_rewrite" orient(o) glob_constr_with_bindings(c) "in" hyp(id) ] ->
      [ Proofview.V82.tactic (cl_rewrite_clause c o AllOccurrences (Some id))]
 | [ "setoid_rewrite" orient(o) glob_constr_with_bindings(c) "at" occurrences(occ) ] ->
      [ Proofview.V82.tactic (cl_rewrite_clause c o (occurrences_of occ) None)]
 | [ "setoid_rewrite" orient(o) glob_constr_with_bindings(c) "at" occurrences(occ) "in" hyp(id)] ->
      [ Proofview.V82.tactic (cl_rewrite_clause c o (occurrences_of occ) (Some id))]
 | [ "setoid_rewrite" orient(o) glob_constr_with_bindings(c) "in" hyp(id) "at" occurrences(occ)] ->
      [ Proofview.V82.tactic (cl_rewrite_clause c o (occurrences_of occ) (Some id))]
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

type binders_argtype = local_binder list

let wit_binders =
 (Genarg.create_arg None "binders" : binders_argtype Genarg.uniform_genarg_type)

let binders = Pcoq.create_generic_entry "binders" (Genarg.rawwit wit_binders)

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
