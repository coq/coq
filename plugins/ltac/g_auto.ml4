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
open Pcoq.Prim
open Pcoq.Constr
open Pltac
open Hints

DECLARE PLUGIN "ltac_plugin"

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
    solve_unification_constraints = true;
    use_hook = Pfedit.solve_by_implicit_tactic ();
    fail_evar = false;
    expand_evars = true
  } in
  let map c env sigma = c env sigma in
  List.map (fun c -> map (Tacinterp.type_uconstr ~flags ist c)) cs

let pr_auto_using_raw _ _ _  = Pptactic.pr_auto_using Ppconstr.pr_constr_expr
let pr_auto_using_glob _ _ _ = Pptactic.pr_auto_using (fun (c,_) ->
    let _, env = Pfedit.get_current_context () in
    Printer.pr_glob_constr_env env c)
let pr_auto_using _ _ _ = Pptactic.pr_auto_using
    (let sigma, env = Pfedit.get_current_context () in
     Printer.pr_closed_glob_env env sigma)

ARGUMENT EXTEND auto_using
  TYPED AS uconstr_list
  PRINTED BY pr_auto_using
  RAW_TYPED AS uconstr_list
  RAW_PRINTED BY pr_auto_using_raw
  GLOB_TYPED AS uconstr_list
  GLOB_PRINTED BY pr_auto_using_glob
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

TACTIC EXTEND unify
| ["unify" constr(x) constr(y) ] -> [ Tactics.unify x y ]
| ["unify" constr(x) constr(y) "with" preident(base)  ] -> [
    let table = try Some (Hints.searchtable_map base) with Not_found -> None in
    match table with
    | None ->
      let msg = str "Hint table " ++ str base ++ str " not found" in
      Tacticals.New.tclZEROMSG msg
    | Some t ->
      let state = Hints.Hint_db.transparent_state t in
      Tactics.unify ~state x y
  ]
END


TACTIC EXTEND convert_concl_no_check
| ["convert_concl_no_check" constr(x) ] -> [ Tactics.convert_concl_no_check x DEFAULTcast ]
END

let pr_pre_hints_path_atom _ _ _ = Hints.pp_hints_path_atom Libnames.pr_qualid
let pr_hints_path_atom _ _ _ = Hints.pp_hints_path_atom Printer.pr_global
let glob_hints_path_atom ist = Hints.glob_hints_path_atom

ARGUMENT EXTEND hints_path_atom
  PRINTED BY pr_hints_path_atom

  GLOBALIZED BY glob_hints_path_atom

  RAW_PRINTED BY pr_pre_hints_path_atom
  GLOB_PRINTED BY pr_hints_path_atom
| [ ne_global_list(g) ] -> [ Hints.PathHints g ]
| [ "_" ] -> [ Hints.PathAny ]
END

let pr_hints_path prc prx pry c = Hints.pp_hints_path c
let pr_pre_hints_path prc prx pry c = Hints.pp_hints_path_gen Libnames.pr_qualid c
let glob_hints_path ist = Hints.glob_hints_path

ARGUMENT EXTEND hints_path
PRINTED BY pr_hints_path

GLOBALIZED BY glob_hints_path
RAW_PRINTED BY pr_pre_hints_path
GLOB_PRINTED BY pr_hints_path

| [ "(" hints_path(p) ")"  ] -> [ p ]
| [ hints_path(p) "*" ] -> [ Hints.PathStar p ]
| [ "emp" ] -> [ Hints.PathEmpty ]
| [ "eps" ] -> [ Hints.PathEpsilon ]
| [ hints_path(p) "|" hints_path(q) ] -> [ Hints.PathOr (p, q) ]
| [ hints_path_atom(a) ] -> [ Hints.PathAtom a ]
| [ hints_path(p) hints_path(q) ] -> [ Hints.PathSeq (p, q) ]
END

ARGUMENT EXTEND opthints
  TYPED AS preident_list_opt
  PRINTED BY pr_hintbases
| [ ":" ne_preident_list(l) ] -> [ Some l ]
| [ ] -> [ None ]
END

VERNAC COMMAND FUNCTIONAL EXTEND HintCut CLASSIFIED AS SIDEFF
| [ "Hint" "Cut" "[" hints_path(p) "]" opthints(dbnames) ] -> [
    fun ~atts ~st -> begin
        let open Vernacinterp in
        let entry = Hints.HintsCutEntry (Hints.glob_hints_path p) in
        Hints.add_hints ~local:(Locality.make_section_locality atts.locality)
          (match dbnames with None -> ["core"] | Some l -> l) entry;
        st
      end
 ]
END

