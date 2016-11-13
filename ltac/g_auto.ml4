(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Pp
open Genarg
open Stdarg
open Pcoq.Prim
open Pcoq.Constr
open Pltac
open Hints
open Tacexpr

DECLARE PLUGIN "g_auto"

(* Hint bases *)


TACTIC EXTEND eassumption
| [ "eassumption" ] -> [ Eauto.e_assumption ]
END

TACTIC EXTEND eexact
| [ "eexact" constr(c) ] -> [ Eauto.e_give_exact c ]
END

let pr_hintbases _prc _prlc _prt = Pptactic.pr_hintbases

ARGUMENT EXTEND hintbases
  TYPED AS preident_list_opt
  PRINTED BY pr_hintbases
| [ "with" "*" ] -> [ None ]
| [ "with" ne_preident_list(l) ] -> [ Some l ]
| [ ] -> [ Some [] ]
END

let eval_uconstrs ist cs =
  let flags = {
    Pretyping.use_typeclasses = false;
    use_unif_heuristics = true;
    use_hook = Some Pfedit.solve_by_implicit_tactic;
    fail_evar = false;
    expand_evars = true
  } in
  let map c = { delayed = fun env sigma ->
    let Sigma.Sigma (c, sigma, p) = c.delayed env sigma in
    Sigma.Sigma (EConstr.of_constr c, sigma, p)
  } in
  List.map (fun c -> map (Pretyping.type_uconstr ~flags ist c)) cs

let pr_auto_using _ _ _ = Pptactic.pr_auto_using (fun _ -> mt ())

ARGUMENT EXTEND auto_using
  TYPED AS uconstr_list
  PRINTED BY pr_auto_using
| [ "using" ne_uconstr_list_sep(l, ",") ] -> [ l ]
| [ ] -> [ [] ]
END

(** Auto *)

TACTIC EXTEND trivial
| [ "trivial" auto_using(lems) hintbases(db) ] ->
    [ Auto.h_trivial (eval_uconstrs ist lems) db ]
END

TACTIC EXTEND info_trivial
| [ "info_trivial" auto_using(lems) hintbases(db) ] ->
    [ Auto.h_trivial ~debug:Info (eval_uconstrs ist lems) db ]
END

TACTIC EXTEND debug_trivial
| [ "debug" "trivial" auto_using(lems) hintbases(db) ] ->
    [ Auto.h_trivial ~debug:Debug (eval_uconstrs ist lems) db ]
END

TACTIC EXTEND auto
| [ "auto" int_or_var_opt(n) auto_using(lems) hintbases(db) ] ->
    [ Auto.h_auto n (eval_uconstrs ist lems) db ]
END

TACTIC EXTEND info_auto
| [ "info_auto" int_or_var_opt(n) auto_using(lems) hintbases(db) ] ->
    [ Auto.h_auto ~debug:Info n (eval_uconstrs ist lems) db ]
END

TACTIC EXTEND debug_auto
| [ "debug" "auto" int_or_var_opt(n) auto_using(lems) hintbases(db) ] ->
    [ Auto.h_auto ~debug:Debug n (eval_uconstrs ist lems) db ]
END

(** Eauto *)

TACTIC EXTEND prolog
| [ "prolog" "[" uconstr_list(l) "]" int_or_var(n) ] ->
    [ Eauto.prolog_tac (eval_uconstrs ist l) n ]
END

let make_depth n = snd (Eauto.make_dimension n None)

TACTIC EXTEND eauto
| [ "eauto" int_or_var_opt(n) int_or_var_opt(p) auto_using(lems)
    hintbases(db) ] ->
    [ Eauto.gen_eauto (Eauto.make_dimension n p) (eval_uconstrs ist lems) db ]
END

TACTIC EXTEND new_eauto
| [ "new" "auto" int_or_var_opt(n) auto_using(lems)
    hintbases(db) ] ->
    [ match db with
      | None -> Auto.new_full_auto (make_depth n) (eval_uconstrs ist lems)
      | Some l -> Auto.new_auto (make_depth n) (eval_uconstrs ist lems) l ]
END

TACTIC EXTEND debug_eauto
| [ "debug" "eauto" int_or_var_opt(n) int_or_var_opt(p) auto_using(lems)
    hintbases(db) ] ->
    [ Eauto.gen_eauto ~debug:Debug (Eauto.make_dimension n p) (eval_uconstrs ist lems) db ]
END

TACTIC EXTEND info_eauto
| [ "info_eauto" int_or_var_opt(n) int_or_var_opt(p) auto_using(lems)
    hintbases(db) ] ->
    [ Eauto.gen_eauto ~debug:Info (Eauto.make_dimension n p) (eval_uconstrs ist lems) db ]
END

TACTIC EXTEND dfs_eauto
| [ "dfs" "eauto" int_or_var_opt(p) auto_using(lems)
      hintbases(db) ] ->
    [ Eauto.gen_eauto (Eauto.make_dimension p None) (eval_uconstrs ist lems) db ]
END

TACTIC EXTEND autounfold
| [ "autounfold" hintbases(db) clause_dft_concl(cl) ] -> [ Eauto.autounfold_tac db cl ]
END

TACTIC EXTEND autounfold_one
| [ "autounfold_one" hintbases(db) "in" hyp(id) ] ->
    [ Eauto.autounfold_one (match db with None -> ["core"] | Some x -> "core"::x) (Some (id, Locus.InHyp)) ]
| [ "autounfold_one" hintbases(db) ] ->
    [ Eauto.autounfold_one (match db with None -> ["core"] | Some x -> "core"::x) None ]
      END

TACTIC EXTEND autounfoldify
| [ "autounfoldify" constr(x) ] -> [
    let db = match Term.kind_of_term x with
      | Term.Const (c,_) -> Names.Label.to_string (Names.con_label c)
      | _ -> assert false
    in Eauto.autounfold ["core";db] Locusops.onConcl 
  ]
END

TACTIC EXTEND unify
| ["unify" constr(x) constr(y) ] -> [ Tactics.unify (EConstr.of_constr x) (EConstr.of_constr y) ]
| ["unify" constr(x) constr(y) "with" preident(base)  ] -> [
    let table = try Some (Hints.searchtable_map base) with Not_found -> None in
    match table with
    | None ->
      let msg = str "Hint table " ++ str base ++ str " not found" in
      Tacticals.New.tclZEROMSG msg
    | Some t ->
      let state = Hints.Hint_db.transparent_state t in
      Tactics.unify ~state (EConstr.of_constr x) (EConstr.of_constr y)
  ]
END


TACTIC EXTEND convert_concl_no_check
| ["convert_concl_no_check" constr(x) ] -> [ Tactics.convert_concl_no_check (EConstr.of_constr x) Term.DEFAULTcast ]
END

let pr_hints_path_atom _ _ _ = Hints.pp_hints_path_atom

ARGUMENT EXTEND hints_path_atom
  PRINTED BY pr_hints_path_atom
| [ ne_global_list(g) ] -> [ Hints.PathHints (List.map Nametab.global g) ]
| [ "_" ] -> [ Hints.PathAny ]
END

let pr_hints_path prc prx pry c = Hints.pp_hints_path c

ARGUMENT EXTEND hints_path
  PRINTED BY pr_hints_path
| [ "(" hints_path(p) ")"  ] -> [ p ]
| [ hints_path(p) "*" ] -> [ Hints.PathStar p ]
| [ "emp" ] -> [ Hints.PathEmpty ]
| [ "eps" ] -> [ Hints.PathEpsilon ]
| [ hints_path(p) "|" hints_path(q) ] -> [ Hints.PathOr (p, q) ]
| [ hints_path_atom(a) ] -> [ Hints.PathAtom a ]
| [ hints_path(p) hints_path(q) ] -> [ Hints.PathSeq (p, q) ]
END

let pr_hintbases _prc _prlc _prt = Pptactic.pr_hintbases

ARGUMENT EXTEND opthints
  TYPED AS preident_list_opt
  PRINTED BY pr_hintbases
| [ ":" ne_preident_list(l) ] -> [ Some l ]
| [ ] -> [ None ]
END

VERNAC COMMAND EXTEND HintCut CLASSIFIED AS SIDEFF
| [ "Hint" "Cut" "[" hints_path(p) "]" opthints(dbnames) ] -> [
  let entry = Hints.HintsCutEntry p in
    Hints.add_hints (Locality.make_section_locality (Locality.LocalityFixme.consume ()))
      (match dbnames with None -> ["core"] | Some l -> l) entry ]
END

