(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Ltac_plugin
open Util
open Pp
open Constrexpr
open Indfun_common
open Indfun
open Genarg
open Stdarg
open Tacarg
open Tactypes
open Pcoq
open Pcoq.Prim
open Pcoq.Constr
open Pltac

DECLARE PLUGIN "recdef_plugin"

let pr_fun_ind_using  prc prlc _ opt_c =
  match opt_c with
    | None -> mt ()
    | Some b -> spc () ++ hov 2 (str "using" ++ spc () ++ Miscprint.pr_with_bindings prc prlc b)

(* Duplication of printing functions because "'a with_bindings" is
   (internally) not uniform in 'a: indeed constr_with_bindings at the
   "typed" level has type "open_constr with_bindings" instead of
   "constr with_bindings"; hence, its printer cannot be polymorphic in
   (prc,prlc)... *)

let pr_fun_ind_using_typed prc prlc _ opt_c =
  match opt_c with
    | None -> mt ()
    | Some b ->
      let env = Global.env () in
      let evd = Evd.from_env env in
      let (_, b) = b env evd in
      spc () ++ hov 2 (str "using" ++ spc () ++ Miscprint.pr_with_bindings prc prlc b)


ARGUMENT EXTEND fun_ind_using
  TYPED AS constr_with_bindings option
  PRINTED BY pr_fun_ind_using_typed
  RAW_TYPED AS constr_with_bindings_opt
  RAW_PRINTED BY pr_fun_ind_using
  GLOB_TYPED AS constr_with_bindings_opt
  GLOB_PRINTED BY pr_fun_ind_using
| [ "using" constr_with_bindings(c) ] -> [ Some c ]
| [ ] -> [ None ]
END


TACTIC EXTEND newfuninv
   [ "functional" "inversion"  quantified_hypothesis(hyp) reference_opt(fname) ] ->
     [
       Proofview.V82.tactic (Invfun.invfun hyp fname)
     ]
END

let pr_intro_as_pat _prc _ _ pat =
  match pat with
    | Some pat ->
      spc () ++ str "as" ++ spc () ++ (* Miscprint.pr_intro_pattern prc  pat *)
        str"<simple_intropattern>"
    | None -> mt ()

let out_disjunctive = CAst.map (function
  | IntroAction (IntroOrAndPattern l) -> l
  | _ -> CErrors.user_err Pp.(str "Disjunctive or conjunctive intro pattern expected."))

ARGUMENT EXTEND with_names TYPED AS intropattern_opt PRINTED BY pr_intro_as_pat
|   [ "as"  simple_intropattern(ipat) ] -> [ Some ipat ]
| []  ->[ None ]
END

let functional_induction b c x pat =
  Proofview.V82.tactic (functional_induction true c x (Option.map out_disjunctive pat))


TACTIC EXTEND newfunind
   ["functional" "induction" ne_constr_list(cl) fun_ind_using(princl) with_names(pat)] ->
     [
       let c = match cl with
	 | [] -> assert false
	 | [c] -> c
	 | c::cl -> EConstr.applist(c,cl)
       in
       Extratactics.onSomeWithHoles (fun x -> functional_induction true c x pat) princl ]
END
(***** debug only ***)
TACTIC EXTEND snewfunind
   ["soft" "functional" "induction" ne_constr_list(cl) fun_ind_using(princl) with_names(pat)] ->
     [
       let c = match cl with
	 | [] -> assert false
	 | [c] -> c
	 | c::cl -> EConstr.applist(c,cl)
       in
       Extratactics.onSomeWithHoles (fun x -> functional_induction false c x pat) princl ]
END


let pr_constr_comma_sequence prc _ _ = prlist_with_sep pr_comma prc

ARGUMENT EXTEND constr_comma_sequence'
  TYPED AS constr_list
  PRINTED BY pr_constr_comma_sequence
| [ constr(c) "," constr_comma_sequence'(l) ] -> [ c::l ]
| [ constr(c) ] -> [ [c] ]
END

let pr_auto_using prc _prlc _prt = Pptactic.pr_auto_using prc

ARGUMENT EXTEND auto_using'
  TYPED AS constr_list
  PRINTED BY pr_auto_using
| [ "using" constr_comma_sequence'(l) ] -> [ l ]
| [ ] -> [ [] ]
END

module Gram = Pcoq.Gram
module Vernac = Pvernac.Vernac_
module Tactic = Pltac

type function_rec_definition_loc_argtype = (Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) Loc.located

let (wit_function_rec_definition_loc : function_rec_definition_loc_argtype Genarg.uniform_genarg_type) =
  Genarg.create_arg "function_rec_definition_loc"

let function_rec_definition_loc =
  Pcoq.create_generic_entry Pcoq.utactic "function_rec_definition_loc" (Genarg.rawwit wit_function_rec_definition_loc)

GEXTEND Gram
  GLOBAL: function_rec_definition_loc ;

  function_rec_definition_loc:
    [ [ g = Vernac.rec_definition -> Loc.tag ~loc:!@loc g ]]
    ;

END

let () =
  let raw_printer _ _ _ (loc,body) = Ppvernac.pr_rec_definition body in
  Pptactic.declare_extra_vernac_genarg_pprule wit_function_rec_definition_loc raw_printer

(* TASSI: n'importe quoi ! *)
VERNAC COMMAND EXTEND Function
   ["Function" ne_function_rec_definition_loc_list_sep(recsl,"with")]
    => [ let hard = List.exists (function
           | _,((_,(_,(CMeasureRec _|CWfRec _)),_,_,_),_) -> true
           | _,((_,(_,CStructRec),_,_,_),_) -> false) recsl in
         match
           Vernac_classifier.classify_vernac
             (Vernacexpr.(VernacExpr([], VernacFixpoint(Decl_kinds.NoDischarge, List.map snd recsl))))
         with
         | Vernacexpr.VtSideff ids, _ when hard ->
             Vernacexpr.(VtStartProof ("Classic", GuaranteesOpacity, ids), VtLater)
         | x -> x ]
    -> [ do_generate_principle false (List.map snd recsl) ]
END

let pr_fun_scheme_arg (princ_name,fun_name,s) =
  Names.Id.print princ_name ++ str " :=" ++ spc() ++ str "Induction for " ++
  Libnames.pr_qualid fun_name ++ spc() ++ str "Sort " ++
  Termops.pr_sort_family s

VERNAC ARGUMENT EXTEND fun_scheme_arg
PRINTED BY pr_fun_scheme_arg
| [ ident(princ_name) ":=" "Induction" "for" reference(fun_name) "Sort" sort_family(s) ] -> [ (princ_name,fun_name,s) ]
END


let warning_error names e =
  let (e, _) = ExplainErr.process_vernac_interp_error (e, Exninfo.null) in
  match e with
    | Building_graph e ->
       let names = pr_enum Libnames.pr_qualid names in
       let error = if do_observe () then (spc () ++ CErrors.print e) else mt () in
       warn_cannot_define_graph (names,error)
    | Defining_principle e ->
       let names = pr_enum Libnames.pr_qualid names in
       let error = if do_observe () then CErrors.print e else mt () in
       warn_cannot_define_principle (names,error)
    | _ -> raise e


VERNAC COMMAND EXTEND NewFunctionalScheme
   ["Functional" "Scheme" ne_fun_scheme_arg_list_sep(fas,"with") ]
   => [ Vernacexpr.VtSideff(List.map pi1 fas), Vernacexpr.VtLater ]
   ->
    [
      begin
	try
	  Functional_principles_types.build_scheme fas
	with Functional_principles_types.No_graph_found ->
	  begin
	    match fas with
	      | (_,fun_name,_)::_ ->
		  begin
		    begin
		      make_graph (Smartlocate.global_with_alias fun_name)
		    end
		  ;
		    try Functional_principles_types.build_scheme fas
		    with Functional_principles_types.No_graph_found ->
		      CErrors.user_err Pp.(str "Cannot generate induction principle(s)")
		      | e when CErrors.noncritical e ->
			  let names = List.map (fun (_,na,_) -> na) fas in
			  warning_error names e

		  end
	      | _ -> assert false (* we can only have non empty  list *)
	  end
	  | e when CErrors.noncritical e ->
	      let names = List.map (fun (_,na,_) -> na) fas in
	      warning_error names e
      end

    ]
END
(***** debug only ***)

VERNAC COMMAND EXTEND NewFunctionalCase
  ["Functional" "Case" fun_scheme_arg(fas) ]
  => [ Vernacexpr.VtSideff[pi1 fas], Vernacexpr.VtLater ]
  -> [ Functional_principles_types.build_case_scheme fas ]
END

(***** debug only ***)
VERNAC COMMAND EXTEND GenerateGraph CLASSIFIED AS QUERY
["Generate" "graph" "for" reference(c)] -> [ make_graph (Smartlocate.global_with_alias c) ]
END
