(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Constr
open Genarg
open Stdarg
open Tacarg
open Extraargs
open Pcoq.Prim
open Pltac
open Mod_subst
open Names
open Tacexpr
open Glob_ops
open CErrors
open Util
open Termops
open Equality
open Namegen
open Tactypes
open Tactics
open Proofview.Notations
open Vernacinterp

DECLARE PLUGIN "ltac_plugin"

(**********************************************************************)
(* replace, discriminate, injection, simplify_eq                      *)
(* cutrewrite, dependent rewrite                                      *)

let with_delayed_uconstr ist c tac =
  let flags = {
    Pretyping.use_typeclasses = false;
    solve_unification_constraints = true;
    use_hook = Pfedit.solve_by_implicit_tactic ();
    fail_evar = false;
    expand_evars = true
  } in
  let c = Tacinterp.type_uconstr ~flags ist c in
  Tacticals.New.tclDELAYEDWITHHOLES false c tac

let replace_in_clause_maybe_by ist c1 c2 cl tac =
  with_delayed_uconstr ist c1
  (fun c1 -> replace_in_clause_maybe_by c1 c2 cl (Option.map (Tacinterp.tactic_of_value ist) tac))

let replace_term ist dir_opt c cl =
  with_delayed_uconstr ist c (fun c -> replace_term dir_opt c cl)

TACTIC EXTEND replace
   ["replace" uconstr(c1) "with" constr(c2) clause(cl) by_arg_tac(tac) ]
-> [ replace_in_clause_maybe_by ist c1 c2 cl tac ]
END

TACTIC EXTEND replace_term_left
  [ "replace"  "->" uconstr(c) clause(cl) ]
  -> [ replace_term ist (Some true) c cl ]
END

TACTIC EXTEND replace_term_right
  [ "replace"  "<-" uconstr(c) clause(cl) ]
  -> [ replace_term ist (Some false) c cl ]
END

TACTIC EXTEND replace_term
  [ "replace" uconstr(c) clause(cl) ]
  -> [ replace_term ist None c cl ]
END

let induction_arg_of_quantified_hyp = function
  | AnonHyp n -> None,ElimOnAnonHyp n
  | NamedHyp id -> None,ElimOnIdent (CAst.make id)

(* Versions *_main must come first!! so that "1" is interpreted as a
   ElimOnAnonHyp and not as a "constr", and "id" is interpreted as a
   ElimOnIdent and not as "constr" *)

let mytclWithHoles tac with_evars c =
  Proofview.Goal.enter begin fun gl ->
    let env = Tacmach.New.pf_env gl in
    let sigma = Tacmach.New.project gl in
    let sigma',c = Tactics.force_destruction_arg with_evars env sigma c in
    Tacticals.New.tclWITHHOLES with_evars (tac with_evars (Some c)) sigma'
  end

let elimOnConstrWithHoles tac with_evars c =
  Tacticals.New.tclDELAYEDWITHHOLES with_evars c
    (fun c -> tac with_evars (Some (None,ElimOnConstr c)))

TACTIC EXTEND simplify_eq
  [ "simplify_eq" ] -> [ dEq ~keep_proofs:None false None ]
| [ "simplify_eq" destruction_arg(c) ] -> [ mytclWithHoles (dEq ~keep_proofs:None) false c ]
END
TACTIC EXTEND esimplify_eq
| [ "esimplify_eq" ] -> [ dEq ~keep_proofs:None true None ]
| [ "esimplify_eq" destruction_arg(c) ] -> [ mytclWithHoles (dEq ~keep_proofs:None) true c ]
END

let discr_main c = elimOnConstrWithHoles discr_tac false c

TACTIC EXTEND discriminate
| [ "discriminate" ] -> [ discr_tac false None ]
| [ "discriminate" destruction_arg(c) ] ->
    [ mytclWithHoles discr_tac false c ]
END
TACTIC EXTEND ediscriminate
| [ "ediscriminate" ] -> [ discr_tac true None ]
| [ "ediscriminate" destruction_arg(c) ] ->
    [ mytclWithHoles discr_tac true c ]
END

let discrHyp id =
  Proofview.tclEVARMAP >>= fun sigma ->
  discr_main (fun env sigma -> (sigma, (EConstr.mkVar id, NoBindings)))

let injection_main with_evars c =
 elimOnConstrWithHoles (injClause None None) with_evars c

TACTIC EXTEND injection
| [ "injection" ] -> [ injClause None None false None ]
| [ "injection" destruction_arg(c) ] -> [ mytclWithHoles (injClause None None) false c ]
END
TACTIC EXTEND einjection
| [ "einjection" ] -> [ injClause None None true None ]
| [ "einjection" destruction_arg(c) ] -> [ mytclWithHoles (injClause None None) true c ]
END
TACTIC EXTEND injection_as
| [ "injection" "as" intropattern_list(ipat)] ->
    [ injClause None (Some ipat) false None ]
| [ "injection" destruction_arg(c) "as" intropattern_list(ipat)] ->
    [ mytclWithHoles (injClause None (Some ipat)) false c ]
END
TACTIC EXTEND einjection_as
| [ "einjection" "as" intropattern_list(ipat)] ->
    [ injClause None (Some ipat) true None ]
| [ "einjection" destruction_arg(c) "as" intropattern_list(ipat)] ->
    [ mytclWithHoles (injClause None (Some ipat)) true c ]
END
TACTIC EXTEND simple_injection
| [ "simple" "injection" ] -> [ simpleInjClause None false None ]
| [ "simple" "injection" destruction_arg(c) ] -> [ mytclWithHoles (simpleInjClause None) false c ]
END

let injHyp id =
  Proofview.tclEVARMAP >>= fun sigma ->
  injection_main false (fun env sigma -> (sigma, (EConstr.mkVar id, NoBindings)))

TACTIC EXTEND dependent_rewrite
| [ "dependent" "rewrite" orient(b) constr(c) ] -> [ rewriteInConcl b c ]
| [ "dependent" "rewrite" orient(b) constr(c) "in" hyp(id) ]
    -> [ rewriteInHyp b c id ]
END

(** To be deprecated?, "cutrewrite (t=u) as <-" is equivalent to
    "replace u with t" or "enough (t=u) as <-" and 
    "cutrewrite (t=u) as ->" is equivalent to "enough (t=u) as ->". *)

TACTIC EXTEND cut_rewrite
| [ "cutrewrite" orient(b) constr(eqn) ] -> [ cutRewriteInConcl b eqn ]
| [ "cutrewrite" orient(b) constr(eqn) "in" hyp(id) ]
    -> [ cutRewriteInHyp b eqn id ]
END

(**********************************************************************)
(* Decompose                                                          *)

TACTIC EXTEND decompose_sum
| [ "decompose" "sum" constr(c) ] -> [ Elim.h_decompose_or c ]
END

TACTIC EXTEND decompose_record
| [ "decompose" "record" constr(c) ] -> [ Elim.h_decompose_and c ]
END

(**********************************************************************)
(* Contradiction                                                      *)

open Contradiction

TACTIC EXTEND absurd
 [ "absurd" constr(c) ] -> [ absurd c ]
END

let onSomeWithHoles tac = function
  | None -> tac None
  | Some c -> Tacticals.New.tclDELAYEDWITHHOLES false c (fun c -> tac (Some c))

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
      auto_multi_rewrite_with (Tacinterp.tactic_of_value ist t) l cl
    ]
END

TACTIC EXTEND autorewrite_star
| [ "autorewrite" "*" "with" ne_preident_list(l) clause(cl) ] ->
    [ auto_multi_rewrite ~conds:AllMatches l cl ]
| [ "autorewrite" "*" "with" ne_preident_list(l) clause(cl) "using" tactic(t) ] ->
  [ auto_multi_rewrite_with ~conds:AllMatches (Tacinterp.tactic_of_value ist t) l cl ]
END

(**********************************************************************)
(* Rewrite star                                                       *)

let rewrite_star ist clause orient occs c (tac : Geninterp.Val.t option) =
  let tac' = Option.map (fun t -> Tacinterp.tactic_of_value ist t, FirstSolved) tac in
  with_delayed_uconstr ist c
    (fun c -> general_rewrite_ebindings_clause clause orient occs ?tac:tac' true true (c,NoBindings) true)

TACTIC EXTEND rewrite_star
| [ "rewrite" "*" orient(o) uconstr(c) "in" hyp(id) "at" occurrences(occ) by_arg_tac(tac) ] ->
    [ rewrite_star ist (Some id) o (occurrences_of occ) c tac ]
| [ "rewrite" "*" orient(o) uconstr(c) "at" occurrences(occ) "in" hyp(id) by_arg_tac(tac) ] ->
    [ rewrite_star ist (Some id) o (occurrences_of occ) c tac ]
| [ "rewrite" "*" orient(o) uconstr(c) "in" hyp(id) by_arg_tac(tac) ] ->
    [ rewrite_star ist (Some id) o Locus.AllOccurrences c tac ]
| [ "rewrite" "*" orient(o) uconstr(c) "at" occurrences(occ) by_arg_tac(tac) ] ->
    [ rewrite_star ist None o (occurrences_of occ) c tac ]
| [ "rewrite" "*" orient(o) uconstr(c) by_arg_tac(tac) ] ->
    [ rewrite_star ist None o Locus.AllOccurrences c tac ]
    END

(**********************************************************************)
(* Hint Rewrite                                                       *)

let add_rewrite_hint ~poly bases ort t lcsr =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let f ce =
    let c, ctx = Constrintern.interp_constr env sigma ce in
    let c = EConstr.to_constr sigma c in
    let ctx =
      let ctx = UState.context_set ctx in
        if poly then ctx
	else (** This is a global universe context that shouldn't be
	       refreshed at every use of the hint, declare it globally. *)
	  (Declare.declare_universe_context false ctx;
           Univ.ContextSet.empty)
    in
      CAst.make ?loc:(Constrexpr_ops.constr_loc ce) ((c, ctx), ort, Option.map (in_gen (rawwit wit_ltac)) t) in
  let eqs = List.map f lcsr in
  let add_hints base = add_rew_rules base eqs in
  List.iter add_hints bases

let classify_hint _ = Vernacexpr.VtSideff [], Vernacexpr.VtLater

VERNAC COMMAND FUNCTIONAL EXTEND HintRewrite CLASSIFIED BY classify_hint
  [ "Hint" "Rewrite" orient(o) ne_constr_list(l) ":" preident_list(bl) ] ->
  [ fun ~atts ~st -> add_rewrite_hint ~poly:atts.polymorphic bl o None l; st ]
| [ "Hint" "Rewrite" orient(o) ne_constr_list(l) "using" tactic(t)
    ":" preident_list(bl) ] ->
  [ fun ~atts ~st -> add_rewrite_hint ~poly:atts.polymorphic bl o (Some t) l; st ]
| [ "Hint" "Rewrite" orient(o) ne_constr_list(l) ] ->
  [ fun ~atts ~st -> add_rewrite_hint ~poly:atts.polymorphic ["core"] o None l; st ]
| [ "Hint" "Rewrite" orient(o) ne_constr_list(l) "using" tactic(t) ] ->
  [ fun ~atts ~st -> add_rewrite_hint ~poly:atts.polymorphic ["core"] o (Some t) l; st ]
END

(**********************************************************************)
(* Refine                                                             *)

open EConstr
open Vars

let constr_flags () = {
  Pretyping.use_typeclasses = true;
  Pretyping.solve_unification_constraints = Pfedit.use_unification_heuristics ();
  Pretyping.use_hook = Pfedit.solve_by_implicit_tactic ();
  Pretyping.fail_evar = false;
  Pretyping.expand_evars = true }

let refine_tac ist simple with_classes c =
  Proofview.Goal.enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    let env = Proofview.Goal.env gl in
    let flags =
      { constr_flags () with Pretyping.use_typeclasses = with_classes } in
    let expected_type = Pretyping.OfType concl in
    let c = Tacinterp.type_uconstr ~flags ~expected_type ist c in
    let update = begin fun sigma ->
      c env sigma
    end in
    let refine = Refine.refine ~typecheck:false update in
    if simple then refine
    else refine <*>
           Tactics.New.reduce_after_refine <*>
           Proofview.shelve_unifiable
  end

TACTIC EXTEND refine
| [ "refine" uconstr(c) ] ->
   [ refine_tac ist false true c ]
END

TACTIC EXTEND simple_refine
| [ "simple" "refine" uconstr(c) ] ->
   [ refine_tac ist true true c ]
END

TACTIC EXTEND notcs_refine
| [ "notypeclasses" "refine" uconstr(c) ] ->
   [ refine_tac ist false false c ]
END

TACTIC EXTEND notcs_simple_refine
| [ "simple" "notypeclasses" "refine" uconstr(c) ] ->
   [ refine_tac ist true false c ]
END

(* Solve unification constraints using heuristics or fail if any remain *)
TACTIC EXTEND solve_constraints
[ "solve_constraints" ] -> [ Refine.solve_constraints ]
END

(**********************************************************************)
(* Inversion lemmas (Leminv)                                          *)

open Inv
open Leminv

let seff id = Vernacexpr.VtSideff [id], Vernacexpr.VtLater

(*VERNAC ARGUMENT EXTEND sort_family
| [ "Set" ] -> [ InSet ]
| [ "Prop" ] -> [ InProp ]
| [ "Type" ] -> [ InType ]
END*)

VERNAC COMMAND FUNCTIONAL EXTEND DeriveInversionClear
| [ "Derive" "Inversion_clear" ident(na) "with" constr(c) "Sort" sort_family(s) ]
  => [ seff na ]
  -> [ fun ~atts ~st ->
      let open Vernacinterp in
      add_inversion_lemma_exn ~poly:atts.polymorphic na c s false inv_clear_tac; st ]

| [ "Derive" "Inversion_clear" ident(na) "with" constr(c) ] => [ seff na ]
  -> [ fun ~atts ~st ->
      let open Vernacinterp in
      add_inversion_lemma_exn ~poly:atts.polymorphic na c Sorts.InProp false inv_clear_tac; st ]
END

VERNAC COMMAND FUNCTIONAL EXTEND DeriveInversion
| [ "Derive" "Inversion" ident(na) "with" constr(c) "Sort" sort_family(s) ]
  => [ seff na ]
  -> [ fun ~atts ~st ->
      let open Vernacinterp in
      add_inversion_lemma_exn ~poly:atts.polymorphic na c s false inv_tac; st ]

| [ "Derive" "Inversion" ident(na) "with" constr(c) ] => [ seff na ]
  -> [ fun ~atts ~st ->
      let open Vernacinterp in
      add_inversion_lemma_exn ~poly:atts.polymorphic na c Sorts.InProp false inv_tac; st ]
END

VERNAC COMMAND FUNCTIONAL EXTEND DeriveDependentInversion
| [ "Derive" "Dependent" "Inversion" ident(na) "with" constr(c) "Sort" sort_family(s) ]
  => [ seff na ]
  -> [  fun ~atts ~st ->
      let open Vernacinterp in
      add_inversion_lemma_exn ~poly:atts.polymorphic na c s true dinv_tac; st ]
END

VERNAC COMMAND FUNCTIONAL EXTEND DeriveDependentInversionClear
| [ "Derive" "Dependent" "Inversion_clear" ident(na) "with" constr(c) "Sort" sort_family(s) ]
  => [ seff na ]
  -> [  fun ~atts ~st ->
      let open Vernacinterp in
      add_inversion_lemma_exn ~poly:atts.polymorphic na c s true dinv_clear_tac; st ]
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

(* TODO: add support for some test similar to g_constr.name_colon so that
   expressions like "evar (list A)" do not raise a syntax error *)
TACTIC EXTEND evar
  [ "evar" test_lpar_id_colon "(" ident(id) ":" lconstr(typ) ")" ] -> [ let_evar (Name.Name id) typ ]
| [ "evar" constr(typ) ] -> [ let_evar Name.Anonymous typ ]
END

TACTIC EXTEND instantiate
  [ "instantiate" "(" ident(id) ":=" lglob(c) ")" ] ->
    [ Tacticals.New.tclTHEN (instantiate_tac_by_name id c) Proofview.V82.nf_evar_goals ]
| [ "instantiate" "(" integer(i) ":=" lglob(c) ")" hloc(hl) ] ->
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
      let lem = EConstr.of_constr lem in
      Tacticals.New.tclTHENLAST
        (apply_with_bindings (lem, ImplicitBindings [x]))
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

let inTransitivity : bool * Constr.t -> obj =
  declare_object {(default_object "TRANSITIVITY-STEPS") with
    cache_function = cache_transitivity_lemma;
    open_function = (fun i o -> if Int.equal i 1 then cache_transitivity_lemma o);
    subst_function = subst_transitivity_lemma;
    classify_function = (fun o -> Substitute o) }

(* Main entry points *)

let add_transitivity_lemma left lem =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let lem',ctx (*FIXME*) = Constrintern.interp_constr env sigma lem in
  let lem' = EConstr.to_constr sigma lem' in
  add_anonymous_leaf (inTransitivity (left,lem'))

(* Vernacular syntax *)

TACTIC EXTEND stepl
| ["stepl" constr(c) "by" tactic(tac) ] -> [ step true c (Tacinterp.tactic_of_value ist tac) ]
| ["stepl" constr(c) ] -> [ step true c (Proofview.tclUNIT ()) ]
END

TACTIC EXTEND stepr
| ["stepr" constr(c) "by" tactic(tac) ] -> [ step false c (Tacinterp.tactic_of_value ist tac) ]
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

let cache_implicit_tactic (_,tac) = match tac with
  | Some tac -> Pfedit.declare_implicit_tactic (Tacinterp.eval_tactic tac)
  | None -> Pfedit.clear_implicit_tactic ()

let subst_implicit_tactic (subst,tac) =
  Option.map (Tacsubst.subst_tactic subst) tac

let inImplicitTactic : glob_tactic_expr option -> obj =
  declare_object {(default_object "IMPLICIT-TACTIC") with
       open_function = (fun i o -> if Int.equal i 1 then cache_implicit_tactic o);
       cache_function = cache_implicit_tactic;
       subst_function = subst_implicit_tactic;
       classify_function = (fun o -> Dispose)}

let warn_deprecated_implicit_tactic =
  CWarnings.create ~name:"deprecated-implicit-tactic" ~category:"deprecated"
    (fun () -> strbrk "Implicit tactics are deprecated")

let declare_implicit_tactic tac =
  let () = warn_deprecated_implicit_tactic () in
  Lib.add_anonymous_leaf (inImplicitTactic (Some (Tacintern.glob_tactic tac)))

let clear_implicit_tactic () =
  let () = warn_deprecated_implicit_tactic () in
  Lib.add_anonymous_leaf (inImplicitTactic None)

VERNAC COMMAND EXTEND ImplicitTactic CLASSIFIED AS SIDEFF
| [ "Declare" "Implicit" "Tactic" tactic(tac) ] -> [ declare_implicit_tactic tac ]
| [ "Clear" "Implicit" "Tactic" ] -> [ clear_implicit_tactic () ]
END




(**********************************************************************)
(*spiwack : Vernac commands for retroknowledge                        *)

VERNAC COMMAND EXTEND RetroknowledgeRegister CLASSIFIED AS SIDEFF
 | [ "Register" constr(c) "as" retroknowledge_field(f) "by" constr(b)] ->
           [ let env = Global.env () in
             let evd = Evd.from_env env in
             let tc,_ctx = Constrintern.interp_constr env evd c in
             let tb,_ctx(*FIXME*) = Constrintern.interp_constr env evd b in
             let tc = EConstr.to_constr evd tc in
             let tb = EConstr.to_constr evd tb in
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
  let occref = if occ > 0 then ref occ else Find_subterm.error_invalid_occurrence [occ] in
  let locref = ref 0 in
  let rec substrec x = match DAst.get x with
    | GVar id ->
        if Id.equal id tid 
        then
	  (decr occref;
	   if Int.equal !occref 0 then x
           else
	     (incr locref;
              DAst.make ~loc:(Loc.make_loc (!locref,0)) @@
              GHole (Evar_kinds.QuestionMark {
                  Evar_kinds.qm_obligation=Evar_kinds.Define true;
                  Evar_kinds.qm_name=Anonymous;
                  Evar_kinds.qm_record_field=None;
              }, IntroAnonymous, None)))
        else x
    | _ -> map_glob_constr_left_to_right substrec x in
  let t' = substrec t
  in
  if !occref > 0 then Find_subterm.error_invalid_occurrence [occ] else t'

let subst_hole_with_term occ tc t =
  let locref = ref 0 in
  let occref = ref occ in
  let rec substrec c = match DAst.get c with
    | GHole (Evar_kinds.QuestionMark {
                Evar_kinds.qm_obligation=Evar_kinds.Define true;
                Evar_kinds.qm_name=Anonymous;
                Evar_kinds.qm_record_field=None;
            }, IntroAnonymous, s) ->
        decr occref;
        if Int.equal !occref 0 then tc
        else
	  (incr locref;
           DAst.make ~loc:(Loc.make_loc (!locref,0)) @@
           GHole (Evar_kinds.QuestionMark {
               Evar_kinds.qm_obligation=Evar_kinds.Define true;
               Evar_kinds.qm_name=Anonymous;
               Evar_kinds.qm_record_field=None;
           },IntroAnonymous,s))
    | _ -> map_glob_constr_left_to_right substrec c
  in
  substrec t

open Tacmach

let hResolve id c occ t =
  Proofview.Goal.enter begin fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  let env = Termops.clear_named_body id (Proofview.Goal.env gl) in
  let concl = Proofview.Goal.concl gl in
  let env_ids = Termops.vars_of_env env in
  let c_raw = Detyping.detype Detyping.Now true env_ids env sigma c in
  let t_raw = Detyping.detype Detyping.Now true env_ids env sigma t in
  let rec resolve_hole t_hole =
    try 
      Pretyping.understand env sigma t_hole
    with
      | Pretype_errors.PretypeError (_,_,Pretype_errors.UnsolvableImplicit _) as e ->
          let (e, info) = CErrors.push e in
          let loc_begin = Option.cata (fun l -> fst (Loc.unloc l)) 0 (Loc.get_loc info) in
          resolve_hole (subst_hole_with_term loc_begin c_raw t_hole)
  in
  let t_constr,ctx = resolve_hole (subst_var_with_hole occ id t_raw) in
  let sigma = Evd.merge_universe_context sigma ctx in
  let t_constr_type = Retyping.get_type_of env sigma t_constr in
  Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
    (change_concl (mkLetIn (Name.Anonymous,t_constr,t_constr_type,concl)))
  end

let hResolve_auto id c t =
  let rec resolve_auto n = 
    try
      hResolve id c n t
    with
    | UserError _ as e -> raise e
    | e when CErrors.noncritical e -> resolve_auto (n+1)
  in
  resolve_auto 1

TACTIC EXTEND hresolve_core
| [ "hresolve_core" "(" ident(id) ":=" constr(c) ")" "at" int_or_var(occ) "in" constr(t) ] -> [ hResolve id c occ t ]
| [ "hresolve_core" "(" ident(id) ":=" constr(c) ")" "in" constr(t) ] -> [ hResolve_auto id c t ]
END

(**
   hget_evar
*)

TACTIC EXTEND hget_evar
| [ "hget_evar" int_or_var(n) ] -> [ Evar_tactics.hget_evar n ]
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
    Coqlib.gen_reference_in_modules "RecursiveDefinition"
      (Coqlib.init_modules @ [["Coq";"Arith";"Le"];["Coq";"Arith";"Lt"]]) s in
  function () -> (coq_base_constant "eq_refl")


(* This is simply an implementation of the case_eq tactic.  this code
  should be replaced by a call to the tactic but I don't know how to
  call it before it is defined. *)
let  mkCaseEq a  : unit Proofview.tactic =
  Proofview.Goal.enter begin fun gl ->
    let type_of_a = Tacmach.New.pf_unsafe_type_of gl a in
    Tacticals.New.pf_constr_of_global (delayed_force refl_equal) >>= fun req ->
    Tacticals.New.tclTHENLIST
         [Tactics.generalize [(mkApp(req, [| type_of_a; a|]))];
          Proofview.Goal.enter begin fun gl ->
            let concl = Proofview.Goal.concl gl in
            let env = Proofview.Goal.env gl in
            (** FIXME: this looks really wrong. Does anybody really use this tactic? *)
            let (_, c) = Tacred.pattern_occs [Locus.OnlyOccurrences [1], a] env (Evd.from_env env) concl in
	    change_concl c
          end;
	  simplest_case a]
  end


let case_eq_intros_rewrite x =
  Proofview.Goal.enter begin fun gl ->
  let n = nb_prod (Tacmach.New.project gl) (Proofview.Goal.concl gl) in
  (* Pp.msgnl (Printer.pr_lconstr x); *)
  Tacticals.New.tclTHENLIST [
      mkCaseEq x;
    Proofview.Goal.enter begin fun gl ->
      let concl = Proofview.Goal.concl gl in
      let hyps = Tacmach.New.pf_ids_set_of_hyps gl in
      let n' = nb_prod (Tacmach.New.project gl) concl in
      let h = fresh_id_in_env hyps (Id.of_string "heq") (Proofview.Goal.env gl)  in
      Tacticals.New.tclTHENLIST [
                    Tacticals.New.tclDO (n'-n-1) intro;
		    introduction h;
		    rewrite_except h]
    end
  ]
  end

let rec find_a_destructable_match sigma t =
  let cl = induction_arg_of_quantified_hyp (NamedHyp (Id.of_string "x")) in
  let cl = [cl, (None, None), None], None in
  let dest = TacAtom (Loc.tag @@ TacInductionDestruct(false, false, cl)) in
  match EConstr.kind sigma t with
    | Case (_,_,x,_) when closed0 sigma x ->
	if isVar sigma x then
	  (* TODO check there is no rel n. *)
	  raise (Found (Tacinterp.eval_tactic dest))
	else
	  (* let _ = Pp.msgnl (Printer.pr_lconstr x)  in *)
	  raise (Found (case_eq_intros_rewrite x))
    | _ -> EConstr.iter sigma (fun c -> find_a_destructable_match sigma c) t
	

let destauto t =
  Proofview.tclEVARMAP >>= fun sigma ->
  try find_a_destructable_match sigma t;
    Tacticals.New.tclZEROMSG (str "No destructable match found")
  with Found tac -> tac

let destauto_in id = 
  Proofview.Goal.enter begin fun gl ->
  let ctype = Tacmach.New.pf_unsafe_type_of gl (mkVar id) in
(*  Pp.msgnl (Printer.pr_lconstr (mkVar id)); *)
(*  Pp.msgnl (Printer.pr_lconstr (ctype)); *)
  destauto ctype
  end

TACTIC EXTEND destauto
| [ "destauto" ] -> [ Proofview.Goal.enter begin fun gl -> destauto (Proofview.Goal.concl gl) end ]
| [ "destauto" "in" hyp(id) ] -> [ destauto_in id ]
END

(**********************************************************************)

(**********************************************************************)
(* A version of abstract constructing transparent terms               *)
(* Introduced by Jason Gross and Benjamin Delaware in June 2016       *)
(**********************************************************************)

TACTIC EXTEND transparent_abstract
| [ "transparent_abstract" tactic3(t) ] -> [ Proofview.Goal.nf_enter begin fun gl ->
      Tactics.tclABSTRACT ~opaque:false None (Tacinterp.tactic_of_value ist t) end ]
| [ "transparent_abstract" tactic3(t) "using" ident(id) ] -> [ Proofview.Goal.nf_enter begin fun gl ->
      Tactics.tclABSTRACT ~opaque:false (Some id) (Tacinterp.tactic_of_value ist t) end ]
END

(* ********************************************************************* *)

TACTIC EXTEND constr_eq
| [ "constr_eq" constr(x) constr(y) ] -> [ Tactics.constr_eq ~strict:false x y ]
END

TACTIC EXTEND constr_eq_strict
| [ "constr_eq_strict" constr(x) constr(y) ] -> [ Tactics.constr_eq ~strict:true x y ]
END

TACTIC EXTEND constr_eq_nounivs
| [ "constr_eq_nounivs" constr(x) constr(y) ] -> [
    Proofview.tclEVARMAP >>= fun sigma ->
    if eq_constr_nounivs sigma x y then Proofview.tclUNIT () else Tacticals.New.tclFAIL 0 (str "Not equal") ]
END

TACTIC EXTEND is_evar
| [ "is_evar" constr(x) ] -> [
    Proofview.tclEVARMAP >>= fun sigma ->
    match EConstr.kind sigma x with
      | Evar _ -> Proofview.tclUNIT ()
      | _ -> Tacticals.New.tclFAIL 0 (str "Not an evar")
    ]
END

TACTIC EXTEND has_evar
| [ "has_evar" constr(x) ] -> [
  Proofview.tclEVARMAP >>= fun sigma ->
  if Evarutil.has_undefined_evars sigma x
  then Proofview.tclUNIT ()
  else Tacticals.New.tclFAIL 0 (str "No evars")
]
END

TACTIC EXTEND is_hyp
| [ "is_var" constr(x) ] -> [
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma x with
    | Var _ ->  Proofview.tclUNIT ()
    | _ -> Tacticals.New.tclFAIL 0 (str "Not a variable or hypothesis") ]
END

TACTIC EXTEND is_fix
| [ "is_fix" constr(x) ] -> [
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma x with
    | Fix _ -> Proofview.tclUNIT ()
    | _ -> Tacticals.New.tclFAIL 0 (Pp.str "not a fix definition") ]
END;;

TACTIC EXTEND is_cofix
| [ "is_cofix" constr(x) ] -> [
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma x with
    | CoFix _ -> Proofview.tclUNIT ()
    | _ -> Tacticals.New.tclFAIL 0 (Pp.str "not a cofix definition") ]
END;;

TACTIC EXTEND is_ind
| [ "is_ind" constr(x) ] -> [
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma x with
    | Ind _ -> Proofview.tclUNIT ()
    | _ -> Tacticals.New.tclFAIL 0 (Pp.str "not an (co)inductive datatype") ]
END;;

TACTIC EXTEND is_constructor
| [ "is_constructor" constr(x) ] -> [
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma x with
    | Construct _ -> Proofview.tclUNIT ()
    | _ -> Tacticals.New.tclFAIL 0 (Pp.str "not a constructor") ]
END;;

TACTIC EXTEND is_proj
| [ "is_proj" constr(x) ] -> [
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma x with
    | Proj _ -> Proofview.tclUNIT ()
    | _ -> Tacticals.New.tclFAIL 0 (Pp.str "not a primitive projection") ]
END;;

TACTIC EXTEND is_const
| [ "is_const" constr(x) ] -> [
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma x with
    | Const _ -> Proofview.tclUNIT ()
    | _ -> Tacticals.New.tclFAIL 0 (Pp.str "not a constant") ]
END;;

(* Command to grab the evars left unresolved at the end of a proof. *)
(* spiwack: I put it in extratactics because it is somewhat tied with
   the semantics of the LCF-style tactics, hence with the classic tactic
   mode. *)
VERNAC COMMAND EXTEND GrabEvars
[ "Grab" "Existential" "Variables" ]
  => [ Vernac_classifier.classify_as_proofstep ]
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

(* Unshelves the goal shelved by the tactic. *)
TACTIC EXTEND unshelve
| [ "unshelve" tactic1(t) ] ->
    [
      Proofview.with_shelf (Tacinterp.tactic_of_value ist t) >>= fun (gls, ()) ->
      let gls = List.map Proofview.with_empty_state gls in
      Proofview.Unsafe.tclGETGOALS >>= fun ogls ->
      Proofview.Unsafe.tclSETGOALS (gls @ ogls)
    ]
END

(* Command to add every unshelved variables to the focus *)
VERNAC COMMAND EXTEND Unshelve
[ "Unshelve" ]
  => [ Vernac_classifier.classify_as_proofstep ]
  -> [ Proof_global.simple_with_current_proof (fun _ p  -> Proof.unshelve p) ]
END

(* Gives up on the goals under focus: the goals are considered solved,
   but the proof cannot be closed until the user goes back and solve
   these goals. *)
TACTIC EXTEND give_up
| [ "give_up" ] ->
    [ Proofview.give_up ]
END

(* cycles [n] goals *)
TACTIC EXTEND cycle
| [ "cycle" int_or_var(n) ] -> [ Proofview.cycle n ]
END

(* swaps goals number [i] and [j] *)
TACTIC EXTEND swap
| [ "swap" int_or_var(i) int_or_var(j) ] -> [ Proofview.swap i j ]
END

(* reverses the list of focused goals *)
TACTIC EXTEND revgoals
| [ "revgoals" ] -> [ Proofview.revgoals ]
END

type cmp =
  | Eq
  | Lt | Le
  | Gt | Ge

type 'i test =
  | Test of cmp * 'i * 'i

let pr_cmp = function
  | Eq -> Pp.str"="
  | Lt -> Pp.str"<"
  | Le -> Pp.str"<="
  | Gt -> Pp.str">"
  | Ge -> Pp.str">="

let pr_cmp' _prc _prlc _prt = pr_cmp

let pr_test_gen f (Test(c,x,y)) =
  Pp.(f x ++ pr_cmp c ++ f y)

let pr_test = pr_test_gen (Pputils.pr_or_var Pp.int)

let pr_test' _prc _prlc _prt = pr_test

let pr_itest = pr_test_gen Pp.int

let pr_itest' _prc _prlc _prt = pr_itest



ARGUMENT EXTEND comparison PRINTED BY pr_cmp'
| [ "="  ] -> [ Eq ]
| [ "<"  ] -> [ Lt ]
| [ "<=" ] -> [ Le ]
| [ ">"  ] -> [ Gt ]
| [ ">=" ] -> [ Ge ]
    END

let interp_test ist gls = function
  | Test (c,x,y) ->
      project gls ,
      Test(c,Tacinterp.interp_int_or_var ist x,Tacinterp.interp_int_or_var ist y)

ARGUMENT EXTEND test
  PRINTED BY pr_itest'
  INTERPRETED BY interp_test
  RAW_PRINTED BY pr_test'
  GLOB_PRINTED BY pr_test'
| [ int_or_var(x) comparison(c) int_or_var(y) ] -> [ Test(c,x,y) ]
END

let interp_cmp = function
  | Eq -> Int.equal
  | Lt -> ((<):int->int->bool)
  | Le -> ((<=):int->int->bool)
  | Gt -> ((>):int->int->bool)
  | Ge -> ((>=):int->int->bool)

let run_test = function
  | Test(c,x,y) -> interp_cmp c x y

let guard tst =
  if run_test tst then
    Proofview.tclUNIT ()
  else
    let msg = Pp.(str"Condition not satisfied:"++ws 1++(pr_itest tst)) in
    Tacticals.New.tclZEROMSG msg


TACTIC EXTEND guard
| [ "guard" test(tst) ] -> [ guard tst ]
END

let decompose l c =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Tacmach.New.project gl in
    let to_ind c =
      if isInd sigma c then fst (destInd sigma c)
      else user_err Pp.(str "not an inductive type")
    in
    let l = List.map to_ind l in
    Elim.h_decompose l c
  end

TACTIC EXTEND decompose
| [ "decompose" "[" ne_constr_list(l) "]" constr(c) ] -> [ decompose l c ]
END

(** library/keys *)

VERNAC COMMAND EXTEND Declare_keys CLASSIFIED AS SIDEFF
| [ "Declare" "Equivalent" "Keys" constr(c) constr(c') ] -> [
  let get_key c =
    let env = Global.env () in
    let evd = Evd.from_env env in
    let (evd, c) = Constrintern.interp_open_constr env evd c in
    let kind c = EConstr.kind evd c in
    Keys.constr_key kind c
  in
  let k1 = get_key c in
  let k2 = get_key c' in
    match k1, k2 with
    | Some k1, Some k2 -> Keys.declare_equiv_keys k1 k2
    | _ -> () ]
END

VERNAC COMMAND EXTEND Print_keys CLASSIFIED AS QUERY
| [ "Print" "Equivalent" "Keys" ] -> [ Feedback.msg_info (Keys.pr_keys Printer.pr_global) ]
END


VERNAC COMMAND EXTEND OptimizeProof
| [ "Optimize" "Proof" ] => [ Vernac_classifier.classify_as_proofstep ] ->
  [ Proof_global.compact_the_proof () ]
| [ "Optimize" "Heap" ] => [ Vernac_classifier.classify_as_proofstep ] ->
  [ Gc.compact () ]
END

(** tactic analogous to "OPTIMIZE HEAP" *)

let tclOPTIMIZE_HEAP =
  Proofview.tclLIFT (Proofview.NonLogical.make (fun () -> Gc.compact ()))

TACTIC EXTEND optimize_heap
| [ "optimize_heap" ] -> [ tclOPTIMIZE_HEAP ]
END
