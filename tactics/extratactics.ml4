(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

open Pp
open Pcoq
open Genarg
open Extraargs
open Mod_subst
open Names
open Tacexpr
open Rawterm
open Tactics
open Util
open Evd
open Equality
open Compat

(**********************************************************************)
(* replace, discriminate, injection, simplify_eq                      *)
(* cutrewrite, dependent rewrite                                      *)

let replace_in_clause_maybe_by (sigma1,c1) c2 in_hyp tac =
  Refiner.tclWITHHOLES false
    (replace_in_clause_maybe_by c1 c2 (glob_in_arg_hyp_to_clause in_hyp))
    sigma1
    (Option.map Tacinterp.eval_tactic tac)

let replace_multi_term dir_opt (sigma,c) in_hyp =
  Refiner.tclWITHHOLES false
    (replace_multi_term dir_opt c)
    sigma
    (glob_in_arg_hyp_to_clause in_hyp)

TACTIC EXTEND replace
   ["replace" open_constr(c1) "with" constr(c2) in_arg_hyp(in_hyp) by_arg_tac(tac) ]
-> [ replace_in_clause_maybe_by c1 c2 in_hyp tac ]
END

TACTIC EXTEND replace_term_left
  [ "replace"  "->" open_constr(c) in_arg_hyp(in_hyp) ]
  -> [ replace_multi_term (Some true) c in_hyp]
END

TACTIC EXTEND replace_term_right
  [ "replace"  "<-" open_constr(c) in_arg_hyp(in_hyp) ]
  -> [replace_multi_term (Some false) c in_hyp]
END

TACTIC EXTEND replace_term
  [ "replace" open_constr(c) in_arg_hyp(in_hyp) ]
  -> [ replace_multi_term None c in_hyp ]
END

let induction_arg_of_quantified_hyp = function
  | AnonHyp n -> ElimOnAnonHyp n
  | NamedHyp id -> ElimOnIdent (Util.dummy_loc,id)

(* Versions *_main must come first!! so that "1" is interpreted as a
   ElimOnAnonHyp and not as a "constr", and "id" is interpreted as a
   ElimOnIdent and not as "constr" *)

let elimOnConstrWithHoles tac with_evars c =
  Refiner.tclWITHHOLES with_evars (tac with_evars) 
    c.sigma (Some (ElimOnConstr c.it))

TACTIC EXTEND simplify_eq_main
| [ "simplify_eq" constr_with_bindings(c) ] ->
    [ elimOnConstrWithHoles dEq false c ]
END
TACTIC EXTEND simplify_eq
  [ "simplify_eq" ] -> [ dEq false None ]
| [ "simplify_eq" quantified_hypothesis(h) ] ->
    [ dEq false (Some (induction_arg_of_quantified_hyp h)) ]
END
TACTIC EXTEND esimplify_eq_main
| [ "esimplify_eq" constr_with_bindings(c) ] ->
    [ elimOnConstrWithHoles dEq true c ]
END
TACTIC EXTEND esimplify_eq
| [ "esimplify_eq" ] -> [ dEq true None ]
| [ "esimplify_eq" quantified_hypothesis(h) ] ->
    [ dEq true (Some (induction_arg_of_quantified_hyp h)) ]
END

TACTIC EXTEND discriminate_main
| [ "discriminate" constr_with_bindings(c) ] ->
    [ elimOnConstrWithHoles discr_tac false c ]
END
TACTIC EXTEND discriminate
| [ "discriminate" ] -> [ discr_tac false None ]
| [ "discriminate" quantified_hypothesis(h) ] ->
    [ discr_tac false (Some (induction_arg_of_quantified_hyp h)) ]
END
TACTIC EXTEND ediscriminate_main
| [ "ediscriminate" constr_with_bindings(c) ] ->
    [ elimOnConstrWithHoles discr_tac true c ]
END
TACTIC EXTEND ediscriminate
| [ "ediscriminate" ] -> [ discr_tac true None ]
| [ "ediscriminate" quantified_hypothesis(h) ] ->
    [ discr_tac true (Some (induction_arg_of_quantified_hyp h)) ]
END

let h_discrHyp id gl =
  h_discriminate_main {it = Term.mkVar id,NoBindings; sigma = Refiner.project gl} gl

TACTIC EXTEND injection_main
| [ "injection" constr_with_bindings(c) ] ->
    [ elimOnConstrWithHoles (injClause []) false c ]
END
TACTIC EXTEND injection
| [ "injection" ] -> [ injClause [] false None ]
| [ "injection" quantified_hypothesis(h) ] ->
    [ injClause [] false (Some (induction_arg_of_quantified_hyp h)) ]
END
TACTIC EXTEND einjection_main
| [ "einjection" constr_with_bindings(c) ] ->
    [ elimOnConstrWithHoles (injClause []) true c ]
END
TACTIC EXTEND einjection
| [ "einjection" ] -> [ injClause [] true None ]
| [ "einjection" quantified_hypothesis(h) ] -> [ injClause [] true (Some (induction_arg_of_quantified_hyp h)) ]
END
TACTIC EXTEND injection_as_main
| [ "injection" constr_with_bindings(c) "as" simple_intropattern_list(ipat)] ->
    [ elimOnConstrWithHoles (injClause ipat) false c ]
END
TACTIC EXTEND injection_as
| [ "injection" "as" simple_intropattern_list(ipat)] ->
    [ injClause ipat false None ]
| [ "injection" quantified_hypothesis(h) "as" simple_intropattern_list(ipat) ] ->
    [ injClause ipat false (Some (induction_arg_of_quantified_hyp h)) ]
END
TACTIC EXTEND einjection_as_main
| [ "einjection" constr_with_bindings(c) "as" simple_intropattern_list(ipat)] ->
    [ elimOnConstrWithHoles (injClause ipat) true c ]
END
TACTIC EXTEND einjection_as
| [ "einjection" "as" simple_intropattern_list(ipat)] ->
    [ injClause ipat true None ]
| [ "einjection" quantified_hypothesis(h) "as" simple_intropattern_list(ipat) ] ->
    [ injClause ipat true (Some (induction_arg_of_quantified_hyp h)) ]
END

let h_injHyp id gl =
  h_injection_main { it = Term.mkVar id,NoBindings; sigma = Refiner.project gl } gl

TACTIC EXTEND dependent_rewrite
| [ "dependent" "rewrite" orient(b) constr(c) ] -> [ rewriteInConcl b c ]
| [ "dependent" "rewrite" orient(b) constr(c) "in" hyp(id) ]
    -> [ rewriteInHyp b c id ]
END

TACTIC EXTEND cut_rewrite
| [ "cutrewrite" orient(b) constr(eqn) ] -> [ cutRewriteInConcl b eqn ]
| [ "cutrewrite" orient(b) constr(eqn) "in" hyp(id) ]
    -> [ cutRewriteInHyp b eqn id ]
END

(**********************************************************************)
(* Contradiction                                                      *)

open Contradiction

TACTIC EXTEND absurd
 [ "absurd" constr(c) ] -> [ absurd c ]
END

let onSomeWithHoles tac = function
  | None -> tac None
  | Some c -> Refiner.tclWITHHOLES false tac c.sigma (Some c.it)

TACTIC EXTEND contradiction
 [ "contradiction" constr_with_bindings_opt(c) ] ->
    [ onSomeWithHoles contradiction c ]
END

(**********************************************************************)
(* AutoRewrite                                                        *)

open Autorewrite

TACTIC EXTEND autorewrite
| [ "autorewrite" "with" ne_preident_list(l) in_arg_hyp(cl) ] ->
    [ auto_multi_rewrite  l (glob_in_arg_hyp_to_clause  cl) ]
| [ "autorewrite" "with" ne_preident_list(l) in_arg_hyp(cl) "using" tactic(t) ] ->
    [
      let cl =  glob_in_arg_hyp_to_clause cl in
      auto_multi_rewrite_with (Tacinterp.eval_tactic t) l cl

    ]
END

TACTIC EXTEND autorewrite_star
| [ "autorewrite" "*" "with" ne_preident_list(l) in_arg_hyp(cl) ] ->
    [ auto_multi_rewrite ~conds:AllMatches l (glob_in_arg_hyp_to_clause  cl) ]
| [ "autorewrite" "*" "with" ne_preident_list(l) in_arg_hyp(cl) "using" tactic(t) ] ->
    [ let cl =  glob_in_arg_hyp_to_clause cl in
	auto_multi_rewrite_with ~conds:AllMatches (Tacinterp.eval_tactic t) l cl ]
END

(**********************************************************************)
(* Rewrite star                                                       *)

let rewrite_star clause orient occs (sigma,c) (tac : glob_tactic_expr option) =
  let tac' = Option.map (fun t -> Tacinterp.eval_tactic t, FirstSolved) tac in
  Refiner. tclWITHHOLES false
    (general_rewrite_ebindings_clause clause orient occs ?tac:tac' true (c,NoBindings)) sigma true

let occurrences_of = function
  | n::_ as nl when n < 0 -> (false,List.map abs nl)
  | nl ->
      if List.exists (fun n -> n < 0) nl then
	error "Illegal negative occurrence number.";
      (true,nl)

TACTIC EXTEND rewrite_star
| [ "rewrite" "*" orient(o) open_constr(c) "in" hyp(id) "at" occurrences(occ) by_arg_tac(tac) ] ->
    [ rewrite_star (Some id) o (occurrences_of occ) c tac ]
| [ "rewrite" "*" orient(o) open_constr(c) "at" occurrences(occ) "in" hyp(id) by_arg_tac(tac) ] ->
    [ rewrite_star (Some id) o (occurrences_of occ) c tac ]
| [ "rewrite" "*" orient(o) open_constr(c) "in" hyp(id) by_arg_tac(tac) ] ->
    [ rewrite_star (Some id) o Termops.all_occurrences c tac ]
| [ "rewrite" "*" orient(o) open_constr(c) "at" occurrences(occ) by_arg_tac(tac) ] ->
    [ rewrite_star None o (occurrences_of occ) c tac ]
| [ "rewrite" "*" orient(o) open_constr(c) by_arg_tac(tac) ] ->
    [ rewrite_star None o Termops.all_occurrences c tac ]
    END

(**********************************************************************)
(* Hint Rewrite                                                       *)

let add_rewrite_hint name ort t lcsr =
  let env = Global.env() and sigma = Evd.empty in
  let f c = Topconstr.constr_loc c, Constrintern.interp_constr sigma env c, ort, t in
  add_rew_rules name (List.map f lcsr)

VERNAC COMMAND EXTEND HintRewrite
  [ "Hint" "Rewrite" orient(o) ne_constr_list(l) ":" preident(b) ] ->
  [ add_rewrite_hint b o (Tacexpr.TacId []) l ]
| [ "Hint" "Rewrite" orient(o) ne_constr_list(l) "using" tactic(t)
    ":" preident(b) ] ->
  [ add_rewrite_hint b o t l ]
| [ "Hint" "Rewrite" orient(o) ne_constr_list(l) ] ->
  [ add_rewrite_hint "core" o (Tacexpr.TacId []) l ]
| [ "Hint" "Rewrite" orient(o) ne_constr_list(l) "using" tactic(t) ] ->
  [ add_rewrite_hint "core" o t l ]
END

(**********************************************************************)
(* Hint Resolve                                                       *)

open Term
open Coqlib

let project_hint pri l2r c =
  let env = Global.env() in
  let c = Constrintern.interp_constr Evd.empty env c in
  let t = Retyping.get_type_of env Evd.empty c in
  let t =
    Tacred.reduce_to_quantified_ref env Evd.empty (Lazy.force coq_iff_ref) t in
  let sign,ccl = decompose_prod_assum t in
  let (a,b) = match snd (decompose_app ccl) with
    | [a;b] -> (a,b)
    | _ -> assert false in
  let p =
    if l2r then build_coq_iff_left_proj () else build_coq_iff_right_proj () in
  let c = Reductionops.whd_beta Evd.empty (mkApp (c,Termops.extended_rel_vect 0 sign)) in
  let c = it_mkLambda_or_LetIn
    (mkApp (p,[|mkArrow a (lift 1 b);mkArrow b (lift 1 a);c|])) sign in
  (pri,true,c)

let add_hints_iff l2r lc n bl =
  Auto.add_hints true bl
    (Auto.HintsResolveEntry (List.map (project_hint n l2r) lc))

VERNAC COMMAND EXTEND HintResolveIffLR
  [ "Hint" "Resolve" "->" ne_constr_list(lc) natural_opt(n)
    ":" preident_list(bl) ] ->
  [ add_hints_iff true lc n bl ]
| [ "Hint" "Resolve" "->" ne_constr_list(lc) natural_opt(n) ] ->
  [ add_hints_iff true lc n ["core"] ]
END
VERNAC COMMAND EXTEND HintResolveIffRL
  [ "Hint" "Resolve" "<-" ne_constr_list(lc) natural_opt(n)
    ":" preident_list(bl) ] ->
  [ add_hints_iff false lc n bl ]
| [ "Hint" "Resolve" "<-" ne_constr_list(lc) natural_opt(n) ] ->
  [ add_hints_iff false lc n ["core"] ]
END

(**********************************************************************)
(* Refine                                                             *)

open Refine

TACTIC EXTEND refine
  [ "refine" casted_open_constr(c) ] -> [ refine c ]
END

let refine_tac = h_refine

(**********************************************************************)
(* Inversion lemmas (Leminv)                                          *)

open Inv
open Leminv

VERNAC COMMAND EXTEND DeriveInversionClear
  [ "Derive" "Inversion_clear" ident(na) hyp(id) ]
  -> [ inversion_lemma_from_goal 1 na id Term.prop_sort false inv_clear_tac ]

| [ "Derive" "Inversion_clear" natural(n) ident(na) hyp(id) ]
  -> [ inversion_lemma_from_goal n na id Term.prop_sort false inv_clear_tac ]

| [ "Derive" "Inversion_clear" ident(na) "with" constr(c) "Sort" sort(s) ]
  -> [ add_inversion_lemma_exn na c s false inv_clear_tac ]

| [ "Derive" "Inversion_clear" ident(na) "with" constr(c) ]
  -> [ add_inversion_lemma_exn na c (Rawterm.RProp Term.Null) false inv_clear_tac ]
END

open Term
open Rawterm

VERNAC COMMAND EXTEND DeriveInversion
| [ "Derive" "Inversion" ident(na) "with" constr(c) "Sort" sort(s) ]
  -> [ add_inversion_lemma_exn na c s false inv_tac ]

| [ "Derive" "Inversion" ident(na) "with" constr(c) ]
  -> [ add_inversion_lemma_exn na c (RProp Null) false inv_tac ]

| [ "Derive" "Inversion" ident(na) hyp(id) ]
  -> [ inversion_lemma_from_goal 1 na id Term.prop_sort false inv_tac ]

| [ "Derive" "Inversion" natural(n) ident(na) hyp(id) ]
  -> [ inversion_lemma_from_goal n na id Term.prop_sort false inv_tac ]
END

VERNAC COMMAND EXTEND DeriveDependentInversion
| [ "Derive" "Dependent" "Inversion" ident(na) "with" constr(c) "Sort" sort(s) ]
  -> [ add_inversion_lemma_exn na c s true dinv_tac ]
    END

VERNAC COMMAND EXTEND DeriveDependentInversionClear
| [ "Derive" "Dependent" "Inversion_clear" ident(na) "with" constr(c) "Sort" sort(s) ]
  -> [ add_inversion_lemma_exn na c s true dinv_clear_tac ]
END

(**********************************************************************)
(* Subst                                                              *)

TACTIC EXTEND subst
| [ "subst" ne_var_list(l) ] -> [ subst l ]
| [ "subst" ] -> [ fun gl -> subst_all gl ]
END

let simple_subst_tactic_flags =
  { only_leibniz = true; rewrite_dependent_proof = false }

TACTIC EXTEND simple_subst
| [ "simple" "subst" ] -> [ subst_all ~flags:simple_subst_tactic_flags ]
END

open Evar_tactics

(**********************************************************************)
(* Evar creation                                                      *)

TACTIC EXTEND evar
  [ "evar" "(" ident(id) ":" lconstr(typ) ")" ] -> [ let_evar (Name id) typ ]
| [ "evar" constr(typ) ] -> [ let_evar Anonymous typ ]
END

open Tacexpr
open Tacticals

TACTIC EXTEND instantiate
  [ "instantiate" "(" integer(i) ":=" raw(c) ")" hloc(hl) ] ->
    [instantiate i c hl  ]
| [ "instantiate" ] -> [ tclNORMEVAR ]
END


(**********************************************************************)
(** Nijmegen "step" tactic for setoid rewriting                       *)

open Tactics
open Tactics
open Libnames
open Rawterm
open Summary
open Libobject
open Lib

(* Registered lemmas are expected to be of the form
     x R y -> y == z -> x R z    (in the right table)
     x R y -> x == z -> z R y    (in the left table)
*)

let transitivity_right_table = ref []
let transitivity_left_table = ref []

(* [step] tries to apply a rewriting lemma; then apply [tac] intended to
   complete to proof of the last hypothesis (assumed to state an equality) *)

let step left x tac =
  let l =
    List.map (fun lem ->
      tclTHENLAST
      (apply_with_bindings (lem, ImplicitBindings [x]))
        tac)
      !(if left then transitivity_left_table else transitivity_right_table)
  in
  tclFIRST l

(* Main function to push lemmas in persistent environment *)

let cache_transitivity_lemma (_,(left,lem)) =
  if left then
    transitivity_left_table  := lem :: !transitivity_left_table
  else
    transitivity_right_table := lem :: !transitivity_right_table

let subst_transitivity_lemma (subst,(b,ref)) = (b,subst_mps subst ref)

let inTransitivity =
  declare_object {(default_object "TRANSITIVITY-STEPS") with
    cache_function = cache_transitivity_lemma;
    open_function = (fun i o -> if i=1 then cache_transitivity_lemma o);
    subst_function = subst_transitivity_lemma;
    classify_function = (fun o -> Substitute o) }

(* Synchronisation with reset *)

let freeze () = !transitivity_left_table, !transitivity_right_table

let unfreeze (l,r) =
  transitivity_left_table := l;
  transitivity_right_table := r

let init () =
  transitivity_left_table := [];
  transitivity_right_table := []

let _ =
  declare_summary "transitivity-steps"
    { freeze_function = freeze;
      unfreeze_function = unfreeze;
      init_function = init }

(* Main entry points *)

let add_transitivity_lemma left lem =
 let lem' = Constrintern.interp_constr Evd.empty (Global.env ()) lem in
  add_anonymous_leaf (inTransitivity (left,lem'))

(* Vernacular syntax *)

TACTIC EXTEND stepl
| ["stepl" constr(c) "by" tactic(tac) ] -> [ step true c (Tacinterp.eval_tactic tac) ]
| ["stepl" constr(c) ] -> [ step true c tclIDTAC ]
END

TACTIC EXTEND stepr
| ["stepr" constr(c) "by" tactic(tac) ] -> [ step false c (Tacinterp.eval_tactic tac) ]
| ["stepr" constr(c) ] -> [ step false c tclIDTAC ]
END

VERNAC COMMAND EXTEND AddStepl
| [ "Declare" "Left" "Step" constr(t) ] ->
    [ add_transitivity_lemma true t ]
END

VERNAC COMMAND EXTEND AddStepr
| [ "Declare" "Right" "Step" constr(t) ] ->
    [ add_transitivity_lemma false t ]
END

VERNAC COMMAND EXTEND ImplicitTactic
| [ "Declare" "Implicit" "Tactic" tactic(tac) ] ->
    [ Tacinterp.declare_implicit_tactic (Tacinterp.interp tac) ]
END




(**********************************************************************)
(*spiwack : Vernac commands for retroknowledge                        *)

VERNAC COMMAND EXTEND RetroknowledgeRegister
 | [ "Register" constr(c) "as" retroknowledge_field(f) "by" constr(b)] ->
           [ let tc = Constrintern.interp_constr Evd.empty (Global.env ()) c in
             let tb = Constrintern.interp_constr Evd.empty (Global.env ()) b in
             Global.register f tc tb ]
END



(**********************************************************************)
(* sozeau: abs/gen for induction on instantiated dependent inductives, using "Ford" induction as
  defined by Conor McBride *)
TACTIC EXTEND generalize_eqs
| ["generalize_eqs" hyp(id) ] -> [ abstract_generalize ~generalize_vars:false id ]
END
TACTIC EXTEND dep_generalize_eqs
| ["dependent" "generalize_eqs" hyp(id) ] -> [ abstract_generalize ~generalize_vars:false ~force_dep:true id ]
END
TACTIC EXTEND generalize_eqs_vars
| ["generalize_eqs_vars" hyp(id) ] -> [ abstract_generalize ~generalize_vars:true id ]
END
TACTIC EXTEND dep_generalize_eqs_vars
| ["dependent" "generalize_eqs_vars" hyp(id) ] -> [ abstract_generalize ~force_dep:true ~generalize_vars:true id ]
END

(** Tactic to automatically simplify hypotheses of the form [Π Δ, x_i = t_i -> T] 
    where [t_i] is closed w.r.t. Δ. Such hypotheses are automatically generated
    during dependent induction. For internal use. *)

TACTIC EXTEND specialize_eqs
[ "specialize_eqs" hyp(id) ] -> [ specialize_eqs id ]
END

(**********************************************************************)
(* A tactic that considers a given occurrence of [c] in [t] and       *)
(* abstract the minimal set of all the occurrences of [c] so that the *)
(* abstraction [fun x -> t[x/c]] is well-typed                        *)
(*                                                                    *)
(* Contributed by Chung-Kil Hur (Winter 2009)                         *)
(**********************************************************************)

let subst_var_with_hole occ tid t = 
  let occref = if occ > 0 then ref occ else Termops.error_invalid_occurrence [occ] in
  let locref = ref 0 in
  let rec substrec = function
    | RVar (_,id) as x -> 
        if id = tid 
        then (decr occref; if !occref = 0 then x
                           else (incr locref; RHole (make_loc (!locref,0),Evd.QuestionMark(Evd.Define true))))
        else x
    | c -> map_rawconstr_left_to_right substrec c in
  let t' = substrec t
  in
  if !occref > 0 then Termops.error_invalid_occurrence [occ] else t'

let subst_hole_with_term occ tc t =
  let locref = ref 0 in
  let occref = ref occ in
  let rec substrec = function
    | RHole (_,Evd.QuestionMark(Evd.Define true)) -> 
        decr occref; if !occref = 0 then tc
                     else (incr locref; RHole (make_loc (!locref,0),Evd.QuestionMark(Evd.Define true)))
    | c -> map_rawconstr_left_to_right substrec c
  in
  substrec t

open Tacmach

let out_arg = function
  | ArgVar _ -> anomaly "Unevaluated or_var variable"
  | ArgArg x -> x

let hResolve id c occ t gl = 
  let sigma = project gl in 
  let env = Termops.clear_named_body id (pf_env gl) in
  let env_ids = Termops.ids_of_context env in
  let env_names = Termops.names_of_rel_context env in
  let c_raw = Detyping.detype true env_ids env_names c in 
  let t_raw = Detyping.detype true env_ids env_names t in 
  let rec resolve_hole t_hole =
    try 
      Pretyping.Default.understand sigma env t_hole
    with 
    | Loc.Exc_located (loc,Pretype_errors.PretypeError (_,_,Pretype_errors.UnsolvableImplicit _)) ->
        resolve_hole (subst_hole_with_term (fst (unloc loc)) c_raw t_hole)
  in
  let t_constr = resolve_hole (subst_var_with_hole occ id t_raw) in
  let t_constr_type = Retyping.get_type_of env sigma t_constr in
  change_in_concl None (mkLetIn (Anonymous,t_constr,t_constr_type,pf_concl gl)) gl

let hResolve_auto id c t gl =
  let rec resolve_auto n = 
    try
      hResolve id c n t gl
    with
    | UserError _ as e -> raise e
    | _ -> resolve_auto (n+1)
  in
  resolve_auto 1

TACTIC EXTEND hresolve_core
| [ "hresolve_core" "(" ident(id) ":=" constr(c) ")" "at" int_or_var(occ) "in" constr(t) ] -> [ hResolve id c (out_arg occ) t ]
| [ "hresolve_core" "(" ident(id) ":=" constr(c) ")" "in" constr(t) ] -> [ hResolve_auto id c t ]
END

(**
   hget_evar
*)

open Evar_refiner
open Sign

let hget_evar n gl =
  let sigma = project gl in
  let evl = evar_list sigma (pf_concl gl) in
  if List.length evl < n then
    error "Not enough uninstantiated existential variables.";
  if n <= 0 then error "Incorrect existential variable index.";
  let ev = List.nth evl (n-1) in
  let ev_type = existential_type sigma ev in
  change_in_concl None (mkLetIn (Anonymous,mkEvar ev,ev_type,pf_concl gl)) gl

TACTIC EXTEND hget_evar
| [ "hget_evar" int_or_var(n) ] -> [ hget_evar (out_arg n) ]
END

(**********************************************************************)

(**********************************************************************)
(* A tactic that reduces one match t with ... by doing destruct t.    *)
(* if t is not a variable, the tactic does                            *)
(* case_eq t;intros ... heq;rewrite heq in *|-. (but heq itself is    *)
(* preserved).                                                        *)
(* Contributed by Julien Forest and Pierre Courtieu (july 2010)       *)
(**********************************************************************)

exception Found of tactic

let rewrite_except h g =
  tclMAP (fun id -> if id = h then tclIDTAC else 
      tclTRY (Equality.general_rewrite_in true Termops.all_occurrences true id (mkVar h) false))
    (Tacmach.pf_ids_of_hyps g) g


let refl_equal = 
  let coq_base_constant s =
    Coqlib.gen_constant_in_modules "RecursiveDefinition"
      (Coqlib.init_modules @ [["Coq";"Arith";"Le"];["Coq";"Arith";"Lt"]]) s in
  function () -> (coq_base_constant "eq_refl")


(* This is simply an implementation of the case_eq tactic.  this code
  should be replaced by a call to the tactic but I don't know how to
  call it before it is defined. *)
let  mkCaseEq a  : tactic =
     (fun g ->
       let type_of_a = Tacmach.pf_type_of g a in
       tclTHENLIST
         [Hiddentac.h_generalize [mkApp(delayed_force refl_equal, [| type_of_a; a|])];
          (fun g2 ->
	    change_in_concl None
	     (Tacred.pattern_occs [((false,[1]), a)] (Tacmach.pf_env g2) Evd.empty (Tacmach.pf_concl g2))
		  g2);
	  simplest_case a] g);;


let case_eq_intros_rewrite x g =
  let n = nb_prod (Tacmach.pf_concl g) in
  Pp.msgnl (Printer.pr_lconstr x); 
  tclTHENLIST [
      mkCaseEq x;
      (fun g -> 
	let n' = nb_prod (Tacmach.pf_concl g) in
	let h = fresh_id (Tacmach.pf_ids_of_hyps g) (id_of_string "heq") g in
	tclTHENLIST [ (tclDO (n'-n-1) intro);
		      Tacmach.introduction h;
		      rewrite_except h] g
      )
    ] g

let rec find_a_destructable_match t =
  match kind_of_term t with
    | Case (_,_,x,_) when closed0 x ->
	if isVar x then
	  (* TODO check there is no rel n. *)
	  raise (Found (Tacinterp.eval_tactic(<:tactic<destruct x>>)))
	else
	  let _ = Pp.msgnl (Printer.pr_lconstr x)  in
	  raise (Found (case_eq_intros_rewrite x))
    | _ -> iter_constr find_a_destructable_match t
	

let destauto t =
  try find_a_destructable_match t;
    error "No destructable match found"
  with Found tac -> tac

let destauto_in id g = 
  let ctype = Tacmach.pf_type_of g (mkVar id) in
  Pp.msgnl (Printer.pr_lconstr (mkVar id)); 
  Pp.msgnl (Printer.pr_lconstr (ctype)); 
  destauto ctype g

TACTIC EXTEND destauto
| [ "destauto" ] -> [ (fun g -> destauto (Tacmach.pf_concl g) g) ]
| [ "destauto" "in" hyp(id) ] -> [ destauto_in id ]
END


(* ********************************************************************* *)
