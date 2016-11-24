(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open CErrors
open Pp
open Decl_expr
open Names
open Nameops

let pr_label = function
    Anonymous -> mt ()
  | Name id -> pr_id id ++ spc () ++ str ":" ++ spc ()

let pr_justification_items pr_constr = function
    Some [] -> mt ()
  | Some (_::_ as l) ->
      spc () ++ str "by" ++ spc () ++
	prlist_with_sep (fun () -> str ",") pr_constr l
  | None -> spc () ++ str "by *"

let pr_justification_method pr_tac = function
    None -> mt ()
  | Some tac ->
      spc () ++ str "using" ++ spc () ++ pr_tac tac

let pr_statement pr_constr st =
  pr_label st.st_label ++ pr_constr st.st_it

let pr_or_thesis pr_this = function
    Thesis Plain -> str "thesis"
  | Thesis (For id) ->
      str "thesis" ++ spc() ++ str "for" ++ spc () ++ pr_id id
  | This c -> pr_this c

let pr_cut pr_constr pr_tac pr_it c =
  hov 1 (pr_it c.cut_stat) ++
    pr_justification_items pr_constr c.cut_by ++
    pr_justification_method pr_tac c.cut_using

let type_or_thesis = function
    Thesis _ -> Term.mkProp
  | This c -> c

let _I x = x

let rec pr_hyps pr_var pr_constr gtyp sep _be _have hyps =
  let pr_sep = if sep then str "and" ++ spc () else mt () in
    match hyps with
	(Hvar _ ::_) as rest ->
	  spc () ++ pr_sep ++ str _have ++
	    pr_vars pr_var pr_constr gtyp false _be _have rest
      | Hprop st :: rest ->
	  begin
	(* let npr_constr env = pr_constr (Environ.push_named (id,None,gtyp st.st_it) env)*) 
	      spc() ++ pr_sep ++ pr_statement pr_constr st ++
		pr_hyps pr_var pr_constr gtyp true _be _have rest
	  end
      | [] -> mt ()

and pr_vars pr_var pr_constr gtyp sep _be _have vars =
  match vars with
    Hvar st :: rest ->
      begin
	(* let npr_constr env = pr_constr (Environ.push_named (id,None,gtyp st.st_it) env)*) 
	let pr_sep = if sep then pr_comma () else mt () in
		spc() ++ pr_sep ++
		  pr_var st ++
		  pr_vars pr_var pr_constr gtyp true _be _have rest
      end
   | (Hprop _ :: _) as rest ->
      let _st =  if _be then
	str "be such that"
      else
	str "such that" in
	spc() ++ _st ++  pr_hyps pr_var pr_constr gtyp false _be _have rest
  | [] -> mt ()

let pr_suffices_clause pr_var pr_constr (hyps,c) =
    pr_hyps pr_var pr_constr _I false false "to have" hyps ++ spc () ++
       str "to show" ++ spc () ++ pr_or_thesis pr_constr c

let pr_elim_type = function
    ET_Case_analysis -> str "cases"
  | ET_Induction -> str "induction"

let pr_block_type = function
    B_elim et -> pr_elim_type et
  | B_proof -> str "proof"
  | B_claim -> str "claim"
  | B_focus -> str "focus"

let pr_casee pr_constr pr_tac =function
    Real c -> str "on" ++ spc () ++ pr_constr c
  | Virtual cut -> str "of" ++ spc () ++ pr_cut pr_constr pr_tac (pr_statement pr_constr) cut

let pr_side = function
    Lhs -> str "=~"
  | Rhs -> str "~="

let rec pr_bare_proof_instr pr_var pr_constr pr_pat pr_tac _then _thus = function
  | Pescape -> str "escape"
  | Pthen i -> pr_bare_proof_instr pr_var pr_constr pr_pat pr_tac  true _thus i
  | Pthus i -> pr_bare_proof_instr pr_var pr_constr pr_pat pr_tac  _then true i
  | Phence i -> pr_bare_proof_instr pr_var pr_constr pr_pat pr_tac true true i
  | Pcut c ->
      begin
	match _then,_thus with
	    false,false -> str "have" ++ spc () ++
	      pr_cut pr_constr pr_tac (pr_statement (pr_or_thesis pr_constr)) c
	  | false,true  -> str "thus" ++ spc () ++
	      pr_cut pr_constr pr_tac (pr_statement (pr_or_thesis pr_constr)) c
	  | true,false  -> str "then" ++ spc () ++
	      pr_cut pr_constr pr_tac (pr_statement (pr_or_thesis pr_constr)) c
	  | true,true   -> str "hence" ++ spc () ++
	      pr_cut pr_constr pr_tac (pr_statement (pr_or_thesis pr_constr)) c
      end
  | Psuffices c ->
      str "suffices" ++  pr_cut pr_constr pr_tac (pr_suffices_clause pr_var pr_constr) c
  | Prew (sid,c) ->
      (if _thus then str "thus" else str "    ") ++ spc () ++
	pr_side sid ++ spc () ++ pr_cut pr_constr pr_tac (pr_statement pr_constr) c
  | Passume hyps ->
      str "assume" ++ pr_hyps pr_var pr_constr _I false false "we have" hyps
  | Plet hyps ->
      str "let" ++ pr_vars pr_var pr_constr _I false true "let" hyps
  | Pclaim st ->
      str "claim" ++ spc () ++ pr_statement pr_constr st
  | Pfocus st ->
      str "focus on" ++ spc () ++ pr_statement pr_constr st
  | Pconsider (id,hyps) ->
      str "consider" ++ pr_vars pr_var pr_constr _I false false "consider" hyps
      ++ spc () ++ str "from " ++ pr_constr id
  | Pgiven hyps ->
      str "given" ++ pr_vars pr_var pr_constr _I false false "given" hyps
  | Ptake witl ->
      str "take" ++ spc () ++
	prlist_with_sep pr_comma pr_constr witl
  | Pdefine (id,args,body) ->
      str "define" ++ spc () ++ pr_id id ++ spc () ++
	prlist_with_sep spc
	(fun st -> str "(" ++
	   pr_var st ++ str ")") args ++ spc () ++
	str "as" ++ (pr_constr body)
  | Pcast (id,typ) ->
      str "reconsider" ++ spc () ++
	pr_or_thesis pr_id id ++ spc () ++
	str "as" ++ spc () ++ (pr_constr typ)
  | Psuppose hyps ->
      str "suppose" ++
	pr_hyps pr_var pr_constr _I false false "we have" hyps 
  | Pcase (params,pat,hyps) ->
      str "suppose it is" ++ spc () ++ pr_pat pat ++
	(if params = [] then mt () else
	   (spc () ++ str "with" ++ spc () ++
	      prlist_with_sep spc
	      (fun st -> str "(" ++
		 pr_var st ++ str ")") params ++ spc ()))
      ++
	(if hyps = [] then mt () else
	   (spc () ++ str "and" ++
	      pr_hyps pr_var (pr_or_thesis pr_constr) type_or_thesis
	      false false "we have" hyps)) 
  | Pper (et,c) -> 
      str "per" ++ spc () ++ pr_elim_type et ++ spc () ++
	pr_casee pr_constr pr_tac c  
  | Pend blk -> str "end" ++ spc () ++ pr_block_type blk

let pr_emph = function
    0 -> str "    "
  | 1 -> str "*   "
  | 2 -> str "**  "
  | 3 -> str "*** "
  | _ -> anomaly (Pp.str "unknown emphasis")

let pr_gen_proof_instr pr_var pr_constr pr_pat pr_tac instr =
  pr_emph instr.emph ++ spc () ++
    pr_bare_proof_instr pr_var pr_constr pr_pat pr_tac false false instr.instr


let pr_raw_proof_instr pconstr1 pconstr2 ptac (instr : raw_proof_instr) =
   pr_gen_proof_instr
     (fun (_,(id,otyp)) -> 
       match otyp with
	 None -> pr_id id
       | Some typ -> str "(" ++ pr_id id ++ str ":" ++ pconstr1 typ ++str ")"
     )
     pconstr2
     Ppconstr.pr_cases_pattern_expr
     (ptac Pptactic.ltop)
     instr

let pr_glob_proof_instr pconstr1 pconstr2 ptac (instr : glob_proof_instr) =
    pr_gen_proof_instr
      (fun (_,(id,otyp)) -> 
	match otyp with
	  None -> pr_id id
	| Some typ -> str "(" ++ pr_id id ++ str ":" ++ pconstr1 typ ++str ")")
     pconstr2
     Ppconstr.pr_cases_pattern_expr
     (ptac Pptactic.ltop)
     instr

let pr_proof_instr pconstr1 pconstr2 ptac (instr : proof_instr) =
  let pconstr1 c = pconstr1 (EConstr.of_constr c) in
  let pconstr2 c = pconstr2 (EConstr.of_constr c) in
  pr_gen_proof_instr
    (fun st -> pr_statement pconstr1 st)
    pconstr2
    (fun mpat -> Ppconstr.pr_cases_pattern_expr mpat.pat_expr)
    (ptac Pptactic.ltop)
    instr

