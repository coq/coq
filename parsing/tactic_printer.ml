(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Sign
open Evd
open Tacexpr
open Decl_expr
open Logic
open Printer

(* arnaud: trucs factices *)
type proof_tree

type rule = Prim of Logic.simple_tactic
                | Nested of (strange*char)
		| Daimon
		| Decl_proof of (string)
			     
and strange =  Tactic of (Pptactic.Proof_type.tactic_expr *bool)
		|Proof_instr of (float array*Decl_expr.proof_instr)

let pr_prim_rule _ = Util.anomaly ""
let is_tactic_proof _ = Util.anomaly ""
let subproof_of_proof _ = Util.anomaly ""
(* arnaud: /trucs factices *)

let pr_tactic = function
  | TacArg (Tacexp t) ->
      (*top tactic from tacinterp*)
      Pptactic.pr_glob_tactic (Global.env()) t
  | t -> 
      Pptactic.pr_tactic (Global.env()) t

let pr_proof_instr instr = 
    Ppdecl_proof.pr_proof_instr (Global.env()) instr

let pr_rule = function
  | Prim r -> hov 0 (pr_prim_rule r)
  | Nested(cmpd,_) ->
      begin
	match cmpd with 
	    Tactic (texp,_) -> hov 0 (pr_tactic texp)
	  | Proof_instr (_,instr) -> hov 0 (pr_proof_instr instr)
      end
  | Daimon -> str "<Daimon>"
  | Decl_proof _ -> str "proof" 

let uses_default_tac = function
  | Nested(Tactic(_,dflt),_) -> dflt
  | _ -> false

(* Does not print change of evars *)
let pr_rule_dot = function 
  | Prim Change_evars -> mt ()
  | r ->
      pr_rule r ++ if uses_default_tac r then str "..." else str"."

exception Different

(* We remove from the var context of env what is already in osign *)
let thin_sign osign sign =
  Sign.fold_named_context
    (fun (id,c,ty as d) sign ->
       try 
	 if Sign.lookup_named id osign = (id,c,ty) then sign
	 else raise Different
       with Not_found | Different -> Environ.push_named_context_val d sign)
    sign ~init:Environ.empty_named_context_val

let rec print_proof sigma osign pf =
  Util.anomaly "" (* arnaud: à restaurer
  let hyps = Environ.named_context_of_val pf.goal.evar_hyps in
  let hyps' = thin_sign osign hyps in
  match pf.ref with
    | None -> 
	hov 0 (pr_goal {pf.goal with evar_hyps=hyps'})
    | Some(r,spfl) ->
    	hov 0 
	  (hov 0 (pr_goal {pf.goal with evar_hyps=hyps'}) ++
	   spc () ++ str" BY " ++
	   hov 0 (pr_rule r) ++ fnl () ++
	   str"  " ++
	   hov 0 (prlist_with_sep pr_fnl (print_proof sigma hyps) spfl))
		  *)
	  
let pr_change gl = 
  str"change " ++
  pr_lconstr_env (Global.env_of_context gl.evar_hyps) gl.evar_concl ++ str"."

let rec print_decl_script tac_printer nochange sigma pf =
  Util.anomaly "" (* arnaud: à restaurer
  match pf.ref with
    | None ->
	(if nochange then 
	   (str"<Your Proof Text here>")
	 else 
	   pr_change pf.goal)
	++ fnl ()
    | Some (Daimon,[]) -> mt ()
    | Some (Prim Change_evars,[subpf]) ->   
	print_decl_script tac_printer nochange sigma subpf
    | Some (Nested(Proof_instr (opened,instr),_) as rule,subprfs) ->
	begin
	  match instr.instr,subprfs with
	    Pescape,[{ref=Some(_,subsubprfs)}] ->
	      hov 7
		(pr_rule_dot rule ++ fnl () ++
		   prlist_with_sep pr_fnl tac_printer subsubprfs) ++ fnl () ++
		if opened then mt () else str "return."
	  | Pclaim _,[body;cont] ->
	      hov 2
		(pr_rule_dot rule ++ fnl () ++
		   print_decl_script tac_printer nochange sigma body) ++ 
		fnl () ++
		if opened then mt () else str "end claim." ++ fnl () ++
		  print_decl_script tac_printer nochange sigma cont
	  | Pfocus _,[body;cont] ->
	      hov 2 
		(pr_rule_dot rule ++ fnl () ++
		   print_decl_script tac_printer nochange sigma body) ++ 
		fnl () ++
		if opened then mt () else str "end focus." ++ fnl () ++
		  print_decl_script tac_printer nochange sigma cont
	  | (Psuppose _ |Pcase (_,_,_)),[body;cont] ->
	      hov 2 
		(pr_rule_dot rule ++ fnl () ++
		   print_decl_script tac_printer nochange sigma body) ++ 
		fnl () ++
		print_decl_script tac_printer nochange sigma cont 
	  | _,[next] ->
	      pr_rule_dot rule ++ fnl () ++
		print_decl_script tac_printer nochange sigma next
	  | _,[] ->
	      pr_rule_dot rule		
	  | _,_ -> anomaly "unknown branching instruction"
	end
    | _ -> anomaly "Not Applicable"
		  *)

let rec print_script nochange sigma pf =
  Util.anomaly "" (* arnaud: à restaurer
  match pf.ref with
    | None ->
        (if nochange then 
	   (str"<Your Tactic Text here>") 
	 else 
	   pr_change pf.goal)
	++ fnl ()
    | Some(Decl_proof opened,script) ->
	assert (List.length script = 1);
	begin
	  if nochange then (mt ()) else (pr_change pf.goal ++ fnl ()) 
	end ++
	  begin
	    hov 0 (str "proof." ++ fnl () ++ 
		     print_decl_script (print_script nochange sigma) 
		     nochange sigma (List.hd script))
	  end ++ fnl () ++
	  begin
	    if opened then mt () else (str "end proof." ++ fnl ())
	  end
    | Some(Daimon,spfl) ->
	((if nochange then (mt ()) else (pr_change pf.goal ++ fnl ())) ++
	   prlist_with_sep pr_fnl
           (print_script nochange sigma) spfl )
    | Some(rule,spfl) ->
	((if nochange then (mt ()) else (pr_change pf.goal ++ fnl ())) ++
	   pr_rule_dot rule ++ fnl () ++
	   prlist_with_sep pr_fnl
           (print_script nochange sigma) spfl )	
		  *)

(* printed by Show Script command *)

let print_treescript nochange sigma pf =
  Util.anomaly "" (* arnaud: à restaurer
  let rec aux pf =
    match pf.ref with
    | None ->
        if nochange then 
	  if pf.goal.evar_extra=None then str"<Your Tactic Text here>"
	  else str"<Your Proof Text here>"
	else pr_change pf.goal
    | Some(Decl_proof opened,script) ->
	assert (List.length script = 1);
	begin
	  if nochange then mt () else pr_change pf.goal ++ fnl ()
	end ++
	  hov 0 
	  begin str "proof." ++ fnl () ++
	    print_decl_script aux
	    nochange sigma (List.hd script) 
	  end ++ fnl () ++ 
	  begin
	    if opened then mt () else (str "end proof." ++ fnl ())
	  end
    | Some(Daimon,spfl) ->
	((if nochange then (mt ()) else (pr_change pf.goal ++ fnl ())) ++
	   prlist_with_sep pr_fnl
           (print_script nochange sigma) spfl )
    | Some(r,spfl) ->
        let indent = if List.length spfl >= 2 then 1 else 0 in
        (if nochange then mt () else (pr_change pf.goal ++ fnl ())) ++
        hv indent (pr_rule_dot r ++ prlist_with_sep fnl aux spfl)
  in hov 0 (aux pf)
		  *)

let rec print_info_script sigma osign pf =
  Util.anomaly "" (* arnaud: à restaurer
  let {evar_hyps=sign; evar_concl=cl} = pf.goal in
  match pf.ref with
    | None -> (mt ())
    | Some(r,spfl) ->
        (pr_rule r ++ 
           match spfl with
             | [pf1] ->
                 if pf1.ref = None then 
		   (str "." ++ fnl ())
                 else 
		   (str";" ++ brk(1,3) ++
		      print_info_script sigma 
		      (Environ.named_context_of_val sign) pf1)
             | _ -> (str"." ++ fnl () ++
                       prlist_with_sep pr_fnl
                         (print_info_script sigma 
			    (Environ.named_context_of_val sign)) spfl))
		  *)

let format_print_info_script sigma osign pf = 
  hov 0 (print_info_script sigma osign pf)
    
let print_subscript sigma sign pf = 
  Util.anomaly "" (* arnaud: à restaurer
  if is_tactic_proof pf then 
    format_print_info_script sigma sign (subproof_of_proof pf)
  else 
    format_print_info_script sigma sign pf

let _ = Refiner.set_info_printer print_subscript
		  *)

