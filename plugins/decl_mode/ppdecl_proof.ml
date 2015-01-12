(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Pp
open Decl_expr
open Names
open Nameops

let pr_constr = Printer.pr_constr_env
let pr_tac = Pptactic.pr_glob_tactic
let pr_pat mpat = Ppconstr.pr_cases_pattern_expr mpat.pat_expr

let pr_label = function
    Anonymous -> mt ()
  | Name id -> pr_id id ++ spc () ++ str ":" ++ spc ()

let pr_constr env c = pr_constr env Evd.empty c

let pr_justification_items env = function
    Some [] -> mt ()
  | Some (_::_ as l) ->
      spc () ++ str "by" ++ spc () ++
	prlist_with_sep (fun () -> str ",") (pr_constr env) l
  | None -> spc () ++ str "by *"

let pr_justification_method env = function
    None -> mt ()
  | Some tac ->
      spc () ++ str "using" ++ spc () ++ pr_tac env tac

let pr_statement pr_it env st =
  pr_label st.st_label ++ pr_it env st.st_it

let pr_or_thesis pr_this env = function
    Thesis Plain -> str "thesis"
  | Thesis (For id) ->
      str "thesis" ++ spc() ++ str "for" ++ spc () ++ pr_id id
  | This c -> pr_this env c

let pr_cut pr_it env c =
  hov 1 (pr_it env c.cut_stat) ++
    pr_justification_items env c.cut_by ++
    pr_justification_method env c.cut_using

let type_or_thesis = function
    Thesis _ -> Term.mkProp
  | This c -> c

let _I x = x

let rec print_hyps pconstr gtyp env sep _be _have hyps =
  let pr_sep = if sep then str "and" ++ spc () else mt () in
    match hyps with
	(Hvar _ ::_) as rest ->
	  spc () ++ pr_sep ++ str _have ++
	    print_vars pconstr gtyp env false _be _have rest
      | Hprop st :: rest ->
	  begin
	    let nenv =
	      match st.st_label with
		  Anonymous -> env
		| Name id -> Environ.push_named (id,None,gtyp st.st_it) env in
	      spc() ++ pr_sep ++ pr_statement pconstr env st ++
		print_hyps pconstr gtyp nenv true _be _have rest
	  end
      | [] -> mt ()

and print_vars pconstr gtyp env sep _be _have vars =
  match vars with
    Hvar st :: rest ->
      begin
	let nenv =
	  match st.st_label with
	      Anonymous -> anomaly (Pp.str "anonymous variable")
	    | Name id -> Environ.push_named (id,None,st.st_it) env in
	let pr_sep = if sep then pr_comma () else mt () in
		spc() ++ pr_sep ++
		   pr_statement pr_constr env st ++
		  print_vars pconstr gtyp nenv true _be _have rest
      end
   | (Hprop _ :: _) as rest ->
      let _st =  if _be then
	str "be such that"
      else
	str "such that" in
	spc() ++ _st ++  print_hyps pconstr gtyp env false _be _have rest
  | [] -> mt ()

let pr_suffices_clause env (hyps,c) =
    print_hyps pr_constr _I env false false "to have" hyps ++ spc () ++
       str "to show" ++ spc () ++ pr_or_thesis pr_constr env c

let pr_elim_type = function
    ET_Case_analysis -> str "cases"
  | ET_Induction -> str "induction"

let pr_casee env =function
    Real c -> str "on" ++ spc () ++ pr_constr env c
  | Virtual cut -> str "of" ++ spc () ++ pr_cut (pr_statement pr_constr) env cut

let pr_side = function
    Lhs -> str "=~"
  | Rhs -> str "~="

let rec pr_bare_proof_instr _then _thus env = function
  | Pescape -> str "escape"
  | Pthen i -> pr_bare_proof_instr true _thus env i
  | Pthus i -> pr_bare_proof_instr _then true env i
  | Phence i -> pr_bare_proof_instr true true env i
  | Pcut c ->
      begin
	match _then,_thus with
	    false,false -> str "have" ++ spc () ++
	      pr_cut (pr_statement (pr_or_thesis pr_constr)) env c
	  | false,true  -> str "thus" ++ spc () ++
	      pr_cut (pr_statement (pr_or_thesis pr_constr)) env c
	  | true,false  -> str "then" ++ spc () ++
	      pr_cut (pr_statement (pr_or_thesis pr_constr)) env c
	  | true,true   -> str "hence" ++ spc () ++
	      pr_cut (pr_statement (pr_or_thesis pr_constr)) env c
      end
  | Psuffices c ->
      str "suffices" ++  pr_cut pr_suffices_clause env c
  | Prew (sid,c) ->
      (if _thus then str "thus" else str "    ") ++ spc () ++
	pr_side sid ++ spc () ++ pr_cut (pr_statement pr_constr) env c
  | Passume hyps ->
      str "assume" ++ print_hyps pr_constr _I env false false "we have" hyps
  | Plet hyps ->
      str "let" ++ print_vars pr_constr _I env false true "let" hyps
  | Pclaim st ->
      str "claim" ++ spc () ++ pr_statement pr_constr env st
  | Pfocus st ->
      str "focus on" ++ spc () ++ pr_statement pr_constr env st
  | Pconsider (id,hyps) ->
      str "consider" ++ print_vars pr_constr _I env false false "consider" hyps
      ++ spc () ++ str "from " ++ pr_constr env id
  | Pgiven hyps ->
      str "given" ++ print_vars pr_constr _I env false false "given" hyps
  | Ptake witl ->
      str "take" ++ spc () ++
	prlist_with_sep pr_comma (pr_constr env) witl
  | Pdefine (id,args,body) ->
      str "define" ++ spc () ++ pr_id id ++ spc () ++
	prlist_with_sep spc
	(fun st -> str "(" ++
	   pr_statement pr_constr env st ++ str ")") args ++ spc () ++
	str "as" ++ (pr_constr env body)
  | Pcast (id,typ) ->
      str "reconsider" ++ spc () ++
	pr_or_thesis (fun _ -> pr_id) env id ++ spc () ++
	str "as" ++ spc () ++ (pr_constr env typ)
  | Psuppose hyps ->
      str "suppose" ++
	print_hyps pr_constr _I env false false "we have" hyps
  | Pcase (params,pat,hyps) ->
      str "suppose it is" ++ spc () ++ pr_pat pat ++
	(if params = [] then mt () else
	   (spc () ++ str "with" ++ spc () ++
	      prlist_with_sep spc
	      (fun st -> str "(" ++
		 pr_statement pr_constr env st ++ str ")") params ++ spc ()))
      ++
	(if hyps = [] then mt () else
	   (spc () ++ str "and" ++
	      print_hyps (pr_or_thesis pr_constr) type_or_thesis
	      env false false "we have" hyps))
  | Pper (et,c) ->
      str "per" ++ spc () ++ pr_elim_type et ++ spc () ++
      pr_casee env c
  | Pend (B_elim et) -> str "end" ++ spc () ++ pr_elim_type et
  | _ -> anomaly (Pp.str "unprintable instruction")

let pr_emph = function
    0 -> str "    "
  | 1 -> str "*   "
  | 2 -> str "**  "
  | 3 -> str "*** "
  | _ -> anomaly (Pp.str "unknown emphasis")

let pr_proof_instr env instr =
  pr_emph instr.emph ++ spc () ++
    pr_bare_proof_instr false false env instr.instr

