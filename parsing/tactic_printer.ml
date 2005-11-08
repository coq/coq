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
open Proof_type
open Proof_trees
open Logic
open Printer

let pr_tactic = function
  | TacArg (Tacexp t) ->
      if !Options.v7 then
	Pptactic.pr_glob_tactic t (*top tactic from tacinterp*)
      else
	Pptacticnew.pr_glob_tactic (Global.env()) t
  | t -> 
      if !Options.v7 then
	Pptactic.pr_tactic t
      else
	Pptacticnew.pr_tactic (Global.env()) t

let pr_rule = function
  | Prim r -> hov 0 (pr_prim_rule r)
  | Tactic (texp,_) -> hov 0 (pr_tactic texp)
  | Change_evars ->
      (* This is internal tactic and cannot be replayed at user-level.
         Function pr_rule_dot below is used when we want to hide
         Change_evars *)
      str "Evar change"

(* Does not print change of evars *)
let pr_rule_dot = function 
  | Change_evars -> mt ()
  | r -> pr_rule r ++ str"."

exception Different

(* We remove from the var context of env what is already in osign *)
let thin_sign osign sign =
  Sign.fold_named_context
    (fun (id,c,ty as d) sign ->
       try 
	 if Sign.lookup_named id osign = (id,c,ty) then sign
	 else raise Different
       with Not_found | Different -> add_named_decl d sign)
    sign ~init:empty_named_context

let rec print_proof sigma osign pf =
  let {evar_hyps=hyps; evar_concl=cl; 
       evar_body=body} = pf.goal in
  let hyps' = thin_sign osign hyps in
  match pf.ref with
    | None -> 
	hov 0 (pr_goal {evar_hyps=hyps'; evar_concl=cl; evar_body=body})
    | Some(r,spfl) ->
    	hov 0 
	  (hov 0 (pr_goal {evar_hyps=hyps'; evar_concl=cl; evar_body=body}) ++
	   spc () ++ str" BY " ++
	   hov 0 (pr_rule r) ++ fnl () ++
	   str"  " ++
	   hov 0 (prlist_with_sep pr_fnl (print_proof sigma hyps) spfl)
)
	  
let pr_change gl = 
  str"Change " ++
  prterm_env (Global.env_of_context gl.evar_hyps) gl.evar_concl ++ str"."

let rec print_script nochange sigma osign pf =
  let {evar_hyps=sign; evar_concl=cl} = pf.goal in
  match pf.ref with
    | None ->
        (if nochange then 
	  (str"<Your Tactic Text here>") 
	else 
	  pr_change pf.goal)
	++ fnl ()
    | Some(r,spfl) ->
        ((if nochange then (mt ()) else (pr_change pf.goal ++ fnl ())) ++
           pr_rule_dot r ++ fnl () ++
           prlist_with_sep pr_fnl
             (print_script nochange sigma sign) spfl)

(* printed by Show Script command *)
let print_treescript nochange sigma _osign pf =
  let rec aux top pf =
    match pf.ref with
    | None ->
        if nochange then 
	  (str"<Your Tactic Text here>") 
	else 
	  (pr_change pf.goal)
    | Some(r,spfl) ->
        (if nochange then mt () else (pr_change pf.goal ++ fnl ())) ++
	pr_rule_dot r ++
	match spfl with
	| [] -> mt ()
	| [spf] -> fnl () ++ (if top then mt () else str "  ") ++ aux top spf
	| _ -> fnl () ++ str " " ++
	    hov 0 (prlist_with_sep fnl (aux false) spfl)
  in hov 0 (aux true pf)

let rec print_info_script sigma osign pf =
  let {evar_hyps=sign; evar_concl=cl} = pf.goal in
  match pf.ref with
    | None -> (mt ())
    | Some(Change_evars,[spf]) ->
        print_info_script sigma osign spf
    | Some(r,spfl) ->
        (pr_rule r ++ 
           match spfl with
             | [pf1] ->
                 if pf1.ref = None then 
		   (str "." ++ fnl ())
                 else 
		   (str";" ++ brk(1,3) ++
		      print_info_script sigma sign pf1)
             | _ -> (str"." ++ fnl () ++
                       prlist_with_sep pr_fnl
                         (print_info_script sigma sign) spfl))

let format_print_info_script sigma osign pf = 
  hov 0 (print_info_script sigma osign pf)
    
let print_subscript sigma sign pf = 
  if is_tactic_proof pf then 
    format_print_info_script sigma sign (subproof_of_proof pf)
  else 
    format_print_info_script sigma sign pf

let _ = Refiner.set_info_printer print_subscript

