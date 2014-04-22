(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Pp
open Genarg
open Extraargs
open Mod_subst
open Names
open Tacexpr
open Glob_ops
open Tactics
open Errors
open Util
open Evd
open Equality
open Misctypes

(**********************************************************************)
(* admit, replace, discriminate, injection, simplify_eq               *)
(* cutrewrite, dependent rewrite                                      *)

TACTIC EXTEND admit
  [ "admit" ] -> [ admit_as_an_axiom ]
END

let replace_in_clause_maybe_by (sigma1,c1) c2 cl  tac =
  Tacticals.New.tclWITHHOLES false
    (replace_in_clause_maybe_by c1 c2 cl)
    sigma1
    (Option.map Tacinterp.eval_tactic tac)

let replace_multi_term dir_opt (sigma,c) cl =
  Tacticals.New.tclWITHHOLES false
    (replace_multi_term dir_opt c)
    sigma
    cl

TACTIC EXTEND replace
   ["replace" open_constr(c1) "with" constr(c2) clause(cl) by_arg_tac(tac) ]
-> [ replace_in_clause_maybe_by c1 c2 cl tac ]
END

TACTIC EXTEND replace_term_left
  [ "replace"  "->" open_constr(c) clause(cl) ]
  -> [ replace_multi_term (Some true) c cl ]
END

TACTIC EXTEND replace_term_right
  [ "replace"  "<-" open_constr(c) clause(cl) ]
  -> [ replace_multi_term (Some false) c cl ]
END

TACTIC EXTEND replace_term
  [ "replace" open_constr(c) clause(cl) ]
  -> [ replace_multi_term None c cl ]
END

let induction_arg_of_quantified_hyp = function
  | AnonHyp n -> ElimOnAnonHyp n
  | NamedHyp id -> ElimOnIdent (Loc.ghost,id)

(* Versions *_main must come first!! so that "1" is interpreted as a
   ElimOnAnonHyp and not as a "constr", and "id" is interpreted as a
   ElimOnIdent and not as "constr" *)

let elimOnConstrWithHoles tac with_evars c =
  Tacticals.New.tclWITHHOLES with_evars (tac with_evars) 
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

let discr_main c = elimOnConstrWithHoles discr_tac false c

TACTIC EXTEND discriminate_main
| [ "discriminate" constr_with_bindings(c) ] ->
    [ discr_main c ]
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

open Proofview.Notations
let discrHyp id =
  Proofview.tclEVARMAP >>= fun sigma ->
  discr_main {it = Term.mkVar id,NoBindings; sigma = sigma;}

let injection_main c =
 elimOnConstrWithHoles (injClause None) false c

TACTIC EXTEND injection_main
| [ "injection" constr_with_bindings(c) ] ->
    [ injection_main c ]
END
TACTIC EXTEND injection
| [ "injection" ] -> [ injClause None false None ]
| [ "injection" quantified_hypothesis(h) ] ->
    [ injClause None false (Some (induction_arg_of_quantified_hyp h)) ]
END
TACTIC EXTEND einjection_main
| [ "einjection" constr_with_bindings(c) ] ->
    [ elimOnConstrWithHoles (injClause None) true c ]
END
TACTIC EXTEND einjection
| [ "einjection" ] -> [ injClause None true None ]
| [ "einjection" quantified_hypothesis(h) ] -> [ injClause None true (Some (induction_arg_of_quantified_hyp h)) ]
END
TACTIC EXTEND injection_as_main
| [ "injection" constr_with_bindings(c) "as" simple_intropattern_list(ipat)] ->
    [ elimOnConstrWithHoles (injClause (Some ipat)) false c ]
END
TACTIC EXTEND injection_as
| [ "injection" "as" simple_intropattern_list(ipat)] ->
    [ injClause (Some ipat) false None ]
| [ "injection" quantified_hypothesis(h) "as" simple_intropattern_list(ipat) ] ->
    [ injClause (Some ipat) false (Some (induction_arg_of_quantified_hyp h)) ]
END
TACTIC EXTEND einjection_as_main
| [ "einjection" constr_with_bindings(c) "as" simple_intropattern_list(ipat)] ->
    [ elimOnConstrWithHoles (injClause (Some ipat)) true c ]
END
TACTIC EXTEND einjection_as
| [ "einjection" "as" simple_intropattern_list(ipat)] ->
    [ injClause (Some ipat) true None ]
| [ "einjection" quantified_hypothesis(h) "as" simple_intropattern_list(ipat) ] ->
    [ injClause (Some ipat) true (Some (induction_arg_of_quantified_hyp h)) ]
END

let injHyp id =
  Proofview.tclEVARMAP >>= fun sigma ->
  injection_main { it = Term.mkVar id,NoBindings; sigma = sigma; }

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
  | Some c -> Tacticals.New.tclWITHHOLES false tac c.sigma (Some c.it)

TACTIC EXTEND contradiction
 [ "contradiction" constr_with_bindings_opt(c) ] ->
    [ onSomeWithHoles contradiction c ]
END

(**********************************************************************)
(* AutoRewrite                                                        *)

open Autorewrite

let pr_orient _prc _prlc _prt = function
  | true -> Pp.mt ()
  | false -> Pp.str " <-"

let pr_orient_string _prc _prlc _prt (orient, s) =
  pr_orient _prc _prlc _prt orient ++ Pp.spc () ++ Pp.str s

ARGUMENT EXTEND orient_string TYPED AS (bool * string) PRINTED BY pr_orient_string
| [ orient(r) preident(i) ] -> [ r, i ]
END

TACTIC EXTEND autorewrite
| [ "autorewrite" "with" ne_preident_list(l) clause(cl) ] ->
    [ auto_multi_rewrite  l ( cl) ]
| [ "autorewrite" "with" ne_preident_list(l) clause(cl) "using" tactic(t) ] ->
    [
      auto_multi_rewrite_with (Tacinterp.eval_tactic t) l cl
    ]
END

TACTIC EXTEND autorewrite_star
| [ "autorewrite" "*" "with" ne_preident_list(l) clause(cl) ] ->
    [ auto_multi_rewrite ~conds:AllMatches l cl ]
| [ "autorewrite" "*" "with" ne_preident_list(l) clause(cl) "using" tactic(t) ] ->
  [ auto_multi_rewrite_with ~conds:AllMatches (Tacinterp.eval_tactic t) l cl ]
END

(**********************************************************************)
(* Rewrite star                                                       *)

let rewrite_star clause orient occs (sigma,c) (tac : glob_tactic_expr option) =
  let tac' = Option.map (fun t -> Tacinterp.eval_tactic t, FirstSolved) tac in
  Tacticals.New. tclWITHHOLES false
    (general_rewrite_ebindings_clause clause orient occs ?tac:tac' true true (c,NoBindings)) sigma true

TACTIC EXTEND rewrite_star
| [ "rewrite" "*" orient(o) open_constr(c) "in" hyp(id) "at" occurrences(occ) by_arg_tac(tac) ] ->
    [ rewrite_star (Some id) o (occurrences_of occ) c tac ]
| [ "rewrite" "*" orient(o) open_constr(c) "at" occurrences(occ) "in" hyp(id) by_arg_tac(tac) ] ->
    [ rewrite_star (Some id) o (occurrences_of occ) c tac ]
| [ "rewrite" "*" orient(o) open_constr(c) "in" hyp(id) by_arg_tac(tac) ] ->
    [ rewrite_star (Some id) o Locus.AllOccurrences c tac ]
| [ "rewrite" "*" orient(o) open_constr(c) "at" occurrences(occ) by_arg_tac(tac) ] ->
    [ rewrite_star None o (occurrences_of occ) c tac ]
| [ "rewrite" "*" orient(o) open_constr(c) by_arg_tac(tac) ] ->
    [ rewrite_star None o Locus.AllOccurrences c tac ]
    END

(**********************************************************************)
(* Hint Rewrite                                                       *)

let add_rewrite_hint bases ort t lcsr =
  let env = Global.env() and sigma = Evd.empty in
  let f c = Constrexpr_ops.constr_loc c, Constrintern.interp_constr sigma env c, ort, t in
  let eqs = List.map f lcsr in
  let add_hints base = add_rew_rules base eqs in
  List.iter add_hints bases

let classify_hint _ = Vernacexpr.VtSideff [], Vernacexpr.VtLater

VERNAC COMMAND EXTEND HintRewrite CLASSIFIED BY classify_hint
  [ "Hint" "Rewrite" orient(o) ne_constr_list(l) ":" preident_list(bl) ] ->
  [ add_rewrite_hint bl o None l ]
| [ "Hint" "Rewrite" orient(o) ne_constr_list(l) "using" tactic(t)
    ":" preident_list(bl) ] ->
  [ add_rewrite_hint bl o (Some t) l ]
| [ "Hint" "Rewrite" orient(o) ne_constr_list(l) ] ->
  [ add_rewrite_hint ["core"] o None l ]
| [ "Hint" "Rewrite" orient(o) ne_constr_list(l) "using" tactic(t) ] ->
  [ add_rewrite_hint ["core"] o (Some t) l ]
END

(**********************************************************************)
(* Hint Resolve                                                       *)

open Term
open Vars
open Coqlib

let project_hint pri l2r r =
  let gr = Smartlocate.global_with_alias r in
  let env = Global.env() in
  let c = Globnames.constr_of_global gr in
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
    (pri,true,Auto.PathAny, Globnames.IsConstr c)

let add_hints_iff l2r lc n bl =
  Auto.add_hints true bl
    (Auto.HintsResolveEntry (List.map (project_hint n l2r) lc))

VERNAC COMMAND EXTEND HintResolveIffLR CLASSIFIED AS SIDEFF
  [ "Hint" "Resolve" "->" ne_global_list(lc) natural_opt(n)
    ":" preident_list(bl) ] ->
  [ add_hints_iff true lc n bl ]
| [ "Hint" "Resolve" "->" ne_global_list(lc) natural_opt(n) ] ->
  [ add_hints_iff true lc n ["core"] ]
END
VERNAC COMMAND EXTEND HintResolveIffRL CLASSIFIED AS SIDEFF
  [ "Hint" "Resolve" "<-" ne_global_list(lc) natural_opt(n)
    ":" preident_list(bl) ] ->
  [ add_hints_iff false lc n bl ]
| [ "Hint" "Resolve" "<-" ne_global_list(lc) natural_opt(n) ] ->
  [ add_hints_iff false lc n ["core"] ]
END

(**********************************************************************)
(* Refine                                                             *)


let refine_red_flags =
  Genredexpr.Lazy {
    Genredexpr.rBeta=true;
    rIota=true;
    rZeta=false;
    rDelta=false;
    rConst=[];
  }

let refine_locs = { Locus.onhyps=None; concl_occs=Locus.AllOccurrences }

let refine_tac (ist, c) =
  Proofview.Goal.enter (fun gl ->
    let env = Proofview.Goal.env gl in
    let constrvars = Tacinterp.extract_ltac_constr_values ist env in
    let vars = (constrvars, ist.Geninterp.lfun) in
    let c = Goal.Refinable.make begin fun h ->
      Goal.bind Goal.concl (fun concl ->
        let flags = Pretyping.all_no_fail_flags in
        let tycon = Pretyping.OfType concl in
        Goal.Refinable.constr_of_raw h tycon flags vars c)
    end in
    Proofview.Goal.lift c begin fun c ->
      Proofview.tclSENSITIVE (Goal.refine c) <*>
      Proofview.V82.tactic (reduce refine_red_flags refine_locs)
    end)

TACTIC EXTEND refine
  [ "refine" glob(c) ] -> [  refine_tac c ]
END

(**********************************************************************)
(* Inversion lemmas (Leminv)                                          *)

open Inv
open Leminv

let seff id = Vernacexpr.VtSideff [id], Vernacexpr.VtLater

VERNAC COMMAND EXTEND DeriveInversionClear
| [ "Derive" "Inversion_clear" ident(na) "with" constr(c) "Sort" sort(s) ]
  => [ seff na ]
  -> [ add_inversion_lemma_exn na c s false inv_clear_tac ]

| [ "Derive" "Inversion_clear" ident(na) "with" constr(c) ] => [ seff na ]
  -> [ add_inversion_lemma_exn na c GProp false inv_clear_tac ]
END

open Term

VERNAC COMMAND EXTEND DeriveInversion
| [ "Derive" "Inversion" ident(na) "with" constr(c) "Sort" sort(s) ]
  => [ seff na ]
  -> [ add_inversion_lemma_exn na c s false inv_tac ]

| [ "Derive" "Inversion" ident(na) "with" constr(c) ] => [ seff na ]
  -> [ add_inversion_lemma_exn na c GProp false inv_tac ]
END

VERNAC COMMAND EXTEND DeriveDependentInversion
| [ "Derive" "Dependent" "Inversion" ident(na) "with" constr(c) "Sort" sort(s) ]
  => [ seff na ]
  -> [ add_inversion_lemma_exn na c s true dinv_tac ]
END

VERNAC COMMAND EXTEND DeriveDependentInversionClear
| [ "Derive" "Dependent" "Inversion_clear" ident(na) "with" constr(c) "Sort" sort(s) ]
  => [ seff na ]
  -> [ add_inversion_lemma_exn na c s true dinv_clear_tac ]
END

(**********************************************************************)
(* Subst                                                              *)

TACTIC EXTEND subst
| [ "subst" ne_var_list(l) ] -> [ subst l ]
| [ "subst" ] -> [ subst_all () ]
END

let simple_subst_tactic_flags =
  { only_leibniz = true; rewrite_dependent_proof = false }

TACTIC EXTEND simple_subst
| [ "simple" "subst" ] -> [ subst_all ~flags:simple_subst_tactic_flags () ]
END

open Evar_tactics

(**********************************************************************)
(* Evar creation                                                      *)

TACTIC EXTEND evar
  [ "evar" "(" ident(id) ":" lconstr(typ) ")" ] -> [ let_evar (Name id) typ ]
| [ "evar" constr(typ) ] -> [ let_evar Anonymous typ ]
END

open Tacticals

TACTIC EXTEND instantiate
  [ "instantiate" "(" integer(i) ":=" lglob(c) ")" hloc(hl) ] ->
    [ Tacticals.New.tclTHEN (instantiate_tac i c hl) Proofview.V82.nf_evar_goals ]
| [ "instantiate" ] -> [ Proofview.V82.nf_evar_goals ]
END


(**********************************************************************)
(** Nijmegen "step" tactic for setoid rewriting                       *)

open Tactics
open Glob_term
open Libobject
open Lib

(* Registered lemmas are expected to be of the form
     x R y -> y == z -> x R z    (in the right table)
     x R y -> x == z -> z R y    (in the left table)
*)

let transitivity_right_table = Summary.ref [] ~name:"transitivity-steps-r"
let transitivity_left_table = Summary.ref [] ~name:"transitivity-steps-l"

(* [step] tries to apply a rewriting lemma; then apply [tac] intended to
   complete to proof of the last hypothesis (assumed to state an equality) *)

let step left x tac =
  let l =
    List.map (fun lem ->
      Tacticals.New.tclTHENLAST
      (Proofview.V82.tactic (apply_with_bindings (lem, ImplicitBindings [x])))
        tac)
      !(if left then transitivity_left_table else transitivity_right_table)
  in
  Tacticals.New.tclFIRST l

(* Main function to push lemmas in persistent environment *)

let cache_transitivity_lemma (_,(left,lem)) =
  if left then
    transitivity_left_table  := lem :: !transitivity_left_table
  else
    transitivity_right_table := lem :: !transitivity_right_table

let subst_transitivity_lemma (subst,(b,ref)) = (b,subst_mps subst ref)

let inTransitivity : bool * constr -> obj =
  declare_object {(default_object "TRANSITIVITY-STEPS") with
    cache_function = cache_transitivity_lemma;
    open_function = (fun i o -> if Int.equal i 1 then cache_transitivity_lemma o);
    subst_function = subst_transitivity_lemma;
    classify_function = (fun o -> Substitute o) }

(* Main entry points *)

let add_transitivity_lemma left lem =
 let lem' = Constrintern.interp_constr Evd.empty (Global.env ()) lem in
  add_anonymous_leaf (inTransitivity (left,lem'))

(* Vernacular syntax *)

TACTIC EXTEND stepl
| ["stepl" constr(c) "by" tactic(tac) ] -> [ step true c (Tacinterp.eval_tactic tac) ]
| ["stepl" constr(c) ] -> [ step true c (Proofview.tclUNIT ()) ]
END

TACTIC EXTEND stepr
| ["stepr" constr(c) "by" tactic(tac) ] -> [ step false c (Tacinterp.eval_tactic tac) ]
| ["stepr" constr(c) ] -> [ step false c (Proofview.tclUNIT ()) ]
END

VERNAC COMMAND EXTEND AddStepl CLASSIFIED AS SIDEFF
| [ "Declare" "Left" "Step" constr(t) ] ->
    [ add_transitivity_lemma true t ]
END

VERNAC COMMAND EXTEND AddStepr CLASSIFIED AS SIDEFF
| [ "Declare" "Right" "Step" constr(t) ] ->
    [ add_transitivity_lemma false t ]
END

VERNAC COMMAND EXTEND ImplicitTactic CLASSIFIED AS SIDEFF
| [ "Declare" "Implicit" "Tactic" tactic(tac) ] ->
    [ Pfedit.declare_implicit_tactic (Tacinterp.interp tac) ]
| [ "Clear" "Implicit" "Tactic" ] ->
    [ Pfedit.clear_implicit_tactic () ]
END




(**********************************************************************)
(*spiwack : Vernac commands for retroknowledge                        *)

VERNAC COMMAND EXTEND RetroknowledgeRegister CLASSIFIED AS SIDEFF
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
[ "specialize_eqs" hyp(id) ] -> [ Proofview.V82.tactic (specialize_eqs id) ]
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
    | GVar (_,id) as x -> 
        if Id.equal id tid 
        then
	  (decr occref;
	   if Int.equal !occref 0 then x
           else
	     (incr locref;
	      GHole (Loc.make_loc (!locref,0),
		     Evar_kinds.QuestionMark(Evar_kinds.Define true), None)))
        else x
    | c -> map_glob_constr_left_to_right substrec c in
  let t' = substrec t
  in
  if !occref > 0 then Termops.error_invalid_occurrence [occ] else t'

let subst_hole_with_term occ tc t =
  let locref = ref 0 in
  let occref = ref occ in
  let rec substrec = function
    | GHole (_,Evar_kinds.QuestionMark(Evar_kinds.Define true),s) ->
        decr occref;
        if Int.equal !occref 0 then tc
        else
	  (incr locref;
	   GHole (Loc.make_loc (!locref,0),
		  Evar_kinds.QuestionMark(Evar_kinds.Define true),s))
    | c -> map_glob_constr_left_to_right substrec c
  in
  substrec t

open Tacmach

let out_arg = function
  | ArgVar _ -> anomaly (Pp.str "Unevaluated or_var variable")
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
      Pretyping.understand sigma env t_hole
    with
      | Pretype_errors.PretypeError (_,_,Pretype_errors.UnsolvableImplicit _) as e ->
          let loc = match Loc.get_loc e with None -> Loc.ghost | Some loc -> loc in
          resolve_hole (subst_hole_with_term (fst (Loc.unloc loc)) c_raw t_hole)
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
    | e when Errors.noncritical e -> resolve_auto (n+1)
  in
  resolve_auto 1

TACTIC EXTEND hresolve_core
| [ "hresolve_core" "(" ident(id) ":=" constr(c) ")" "at" int_or_var(occ) "in" constr(t) ] -> [ Proofview.V82.tactic (hResolve id c (out_arg occ) t) ]
| [ "hresolve_core" "(" ident(id) ":=" constr(c) ")" "in" constr(t) ] -> [ Proofview.V82.tactic (hResolve_auto id c t) ]
END

(**
   hget_evar
*)

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
| [ "hget_evar" int_or_var(n) ] -> [ Proofview.V82.tactic (hget_evar (out_arg n)) ]
END

(**********************************************************************)

(**********************************************************************)
(* A tactic that reduces one match t with ... by doing destruct t.    *)
(* if t is not a variable, the tactic does                            *)
(* case_eq t;intros ... heq;rewrite heq in *|-. (but heq itself is    *)
(* preserved).                                                        *)
(* Contributed by Julien Forest and Pierre Courtieu (july 2010)       *)
(**********************************************************************)

exception Found of unit Proofview.tactic

let rewrite_except h =
  Proofview.Goal.enter begin fun gl ->
  let hyps = Tacmach.New.pf_ids_of_hyps gl in
  Tacticals.New.tclMAP (fun id -> if Id.equal id h then Proofview.tclUNIT () else 
      Tacticals.New.tclTRY (Equality.general_rewrite_in true Locus.AllOccurrences true true id (mkVar h) false))
    hyps
  end


let refl_equal = 
  let coq_base_constant s =
    Coqlib.gen_constant_in_modules "RecursiveDefinition"
      (Coqlib.init_modules @ [["Coq";"Arith";"Le"];["Coq";"Arith";"Lt"]]) s in
  function () -> (coq_base_constant "eq_refl")


(* This is simply an implementation of the case_eq tactic.  this code
  should be replaced by a call to the tactic but I don't know how to
  call it before it is defined. *)
let  mkCaseEq a  : unit Proofview.tactic =
  Proofview.Goal.enter begin fun gl ->
    let type_of_a = Tacmach.New.of_old (fun g -> Tacmach.pf_type_of g a) gl in
       Tacticals.New.tclTHENLIST
         [Proofview.V82.tactic (Tactics.Simple.generalize [mkApp(delayed_force refl_equal, [| type_of_a; a|])]);
          Proofview.Goal.enter begin fun gl ->
            let concl = Proofview.Goal.concl gl in
            let env = Proofview.Goal.env gl in
            Proofview.V82.tactic begin
	      change_in_concl None
	        (Tacred.pattern_occs [Locus.OnlyOccurrences [1], a] env Evd.empty concl)
            end
          end;
	  simplest_case a]
  end


let case_eq_intros_rewrite x =
  Proofview.Goal.enter begin fun gl ->
  let n = nb_prod (Proofview.Goal.concl gl) in
  (* Pp.msgnl (Printer.pr_lconstr x); *)
  Tacticals.New.tclTHENLIST [
      mkCaseEq x;
    Proofview.Goal.enter begin fun gl ->
      let concl = Proofview.Goal.concl gl in
      let hyps = Tacmach.New.pf_ids_of_hyps gl in
      let n' = nb_prod concl in
      let h = Tacmach.New.of_old (fun g -> fresh_id hyps (Id.of_string "heq") g) gl in
      Tacticals.New.tclTHENLIST [
                    Tacticals.New.tclDO (n'-n-1) intro;
		    Proofview.V82.tactic (Tacmach.introduction h);
		    rewrite_except h]
    end
  ]
  end

let rec find_a_destructable_match t =
  match kind_of_term t with
    | Case (_,_,x,_) when closed0 x ->
	if isVar x then
	  (* TODO check there is no rel n. *)
	  raise (Found (Tacinterp.eval_tactic(<:tactic<destruct x>>)))
	else
	  (* let _ = Pp.msgnl (Printer.pr_lconstr x)  in *)
	  raise (Found (case_eq_intros_rewrite x))
    | _ -> iter_constr find_a_destructable_match t
	

let destauto t =
  try find_a_destructable_match t;
    Proofview.tclZERO (UserError ("",  str"No destructable match found"))
  with Found tac -> tac

let destauto_in id = 
  Proofview.Goal.enter begin fun gl ->
  let ctype = Tacmach.New.of_old (fun g -> Tacmach.pf_type_of g (mkVar id)) gl in
(*  Pp.msgnl (Printer.pr_lconstr (mkVar id)); *)
(*  Pp.msgnl (Printer.pr_lconstr (ctype)); *)
  destauto ctype
  end

TACTIC EXTEND destauto
| [ "destauto" ] -> [ Proofview.Goal.enter (fun gl -> destauto (Proofview.Goal.concl gl)) ]
| [ "destauto" "in" hyp(id) ] -> [ destauto_in id ]
END


(* ********************************************************************* *)

TACTIC EXTEND constr_eq
| [ "constr_eq" constr(x) constr(y) ] -> [
    if eq_constr x y then Proofview.tclUNIT () else Tacticals.New.tclFAIL 0 (str "Not equal") ]
END

TACTIC EXTEND is_evar
| [ "is_evar" constr(x) ] ->
    [ match kind_of_term x with
        | Evar _ -> Proofview.tclUNIT ()
        | _ -> Tacticals.New.tclFAIL 0 (str "Not an evar")
    ]
END

let rec has_evar x =
  match kind_of_term x with
    | Evar _ -> true
    | Rel _ | Var _ | Meta _ | Sort _ | Const _ | Ind _ | Construct _ ->
      false
    | Cast (t1, _, t2) | Prod (_, t1, t2) | Lambda (_, t1, t2) ->
      has_evar t1 || has_evar t2
    | LetIn (_, t1, t2, t3) ->
      has_evar t1 || has_evar t2 || has_evar t3
    | App (t1, ts) ->
      has_evar t1 || has_evar_array ts
    | Case (_, t1, t2, ts) ->
      has_evar t1 || has_evar t2 || has_evar_array ts
    | Fix ((_, tr)) | CoFix ((_, tr)) ->
      has_evar_prec tr
and has_evar_array x =
  Array.exists has_evar x
and has_evar_prec (_, ts1, ts2) =
  Array.exists has_evar ts1 || Array.exists has_evar ts2

TACTIC EXTEND has_evar
| [ "has_evar" constr(x) ] ->
    [ if has_evar x then Proofview.tclUNIT () else Tacticals.New.tclFAIL 0 (str "No evars") ]
END

TACTIC EXTEND is_hyp
| [ "is_var" constr(x) ] ->
  [ match kind_of_term x with
    | Var _ ->  Proofview.tclUNIT ()
    | _ -> Tacticals.New.tclFAIL 0 (str "Not a variable or hypothesis") ]
END

TACTIC EXTEND is_fix
| [ "is_fix" constr(x) ] ->
  [ match kind_of_term x with
    | Fix _ -> Proofview.tclUNIT ()
    | _ -> Tacticals.New.tclFAIL 0 (Pp.str "not a fix definition") ]
END;;

(* Command to grab the evars left unresolved at the end of a proof. *)
(* spiwack: I put it in extratactics because it is somewhat tied with
   the semantics of the LCF-style tactics, hence with the classic tactic
   mode. *)
VERNAC COMMAND EXTEND GrabEvars
[ "Grab" "Existential" "Variables" ]
  => [ Vernacexpr.VtProofStep, Vernacexpr.VtLater ]
  -> [ Proof_global.simple_with_current_proof (fun _ p  -> Proof.V82.grab_evars p) ]
END

(* Shelves all the goals under focus. *)
TACTIC EXTEND shelve
| [ "shelve" ] ->
    [ Proofview.shelve ]
END

(* Shelves the unifiable goals under focus, i.e. the goals which
   appear in other goals under focus (the unfocused goals are not
   considered). *)
TACTIC EXTEND shelve_unifiable
| [ "shelve_unifiable" ] ->
    [ Proofview.shelve_unifiable ]
END

(* Command to add every unshelved variables to the focus *)
VERNAC COMMAND EXTEND Unshelve
[ "Unshelve" ]
  => [ Vernacexpr.VtProofStep, Vernacexpr.VtLater ]
  -> [ Proof_global.simple_with_current_proof (fun _ p  -> Proof.unshelve p) ]
END

(* Gives up on the goals under focus: the goals are considered solved,
   but the proof cannot be closed until the user goes back and solve
   these goals. *)
TACTIC EXTEND give_up
| [ "give_up" ] ->
    [ Proofview.give_up ]
END
