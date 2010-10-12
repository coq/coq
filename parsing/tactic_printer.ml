(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Sign
open Evd
open Tacexpr
open Proof_type
open Logic
open Printer

let pr_tactic = function
  | TacArg (Tacexp t) ->
      (*top tactic from tacinterp*)
      Pptactic.pr_glob_tactic (Global.env()) t
  | t ->
      Pptactic.pr_tactic (Global.env()) t

let pr_rule = function
  | Prim r -> hov 0 (pr_prim_rule r)
  | Nested(cmpd,_) ->
      begin
	match cmpd with
	  | Tactic (texp,_) -> hov 0 (pr_tactic texp)
      end
  | Daimon -> str "<Daimon>"
  | Decl_proof _ -> str "proof"

let uses_default_tac = function
  | Nested(Tactic(_,dflt),_) -> dflt
  | _ -> false

(* Does not print change of evars *)
let pr_rule_dot = function
  | Prim Change_evars ->str "PC: ch_evars" ++  mt ()
      (* PC: this might be redundant *)
  | r ->
      pr_rule r ++ if uses_default_tac r then str "..." else str"."

let pr_rule_dot_fnl = function
  | Nested (Tactic (TacAtom (_,(TacMutualFix (true,_,_,_)
                              | TacMutualCofix (true,_,_))),_),_) ->
      (* Very big hack to not display hidden tactics in "Theorem with" *)
      (* (would not scale!) *)
      mt ()
   | Prim Change_evars -> mt ()
   | r -> pr_rule_dot r ++ fnl ()

exception Different

let rec print_proof sigma osign pf =
  (* spiwack: [osign] is currently ignored, not sure if this function is even used. *)
  let hyps = Environ.named_context_of_val (Goal.V82.hyps sigma pf.goal) in
  match pf.ref with
    | None ->
	hov 0 (pr_goal {sigma = sigma; it=pf.goal })
    | Some(r,spfl) ->
    	hov 0
	  (hov 0 (pr_goal {sigma = sigma; it=pf.goal }) ++
	   spc () ++ str" BY " ++
	   hov 0 (pr_rule r) ++ fnl () ++
	   str"  " ++
	   hov 0 (prlist_with_sep pr_fnl (print_proof sigma hyps) spfl))

let pr_change sigma gl =
  str"change " ++
  pr_lconstr_env (Goal.V82.env sigma gl) (Goal.V82.concl sigma gl) ++ str"."

let print_decl_script tac_printer ?(nochange=true) sigma pf =
  let rec print_prf pf =
  match pf.ref with
    | None ->
	(if nochange then
	   (str"<Your Proof Text here>")
	 else
	   pr_change sigma pf.goal)
	++ fnl ()
    | Some (Daimon,[]) -> str "(* Some proof has been skipped here *)"
    | Some (Prim Change_evars,[subpf]) -> print_prf subpf
    | _ -> anomaly "Not Applicable" in
  print_prf pf

let print_script ?(nochange=true) sigma pf =
  let rec print_prf pf =
  match pf.ref with
    | None ->
        (if nochange then
	   (str"<Your Tactic Text here>")
	 else
	   pr_change sigma pf.goal)
	++ fnl ()
    | Some(Decl_proof opened,script) ->
	assert (List.length script = 1);
	begin
	  if nochange then (mt ()) else (pr_change sigma pf.goal ++ fnl ())
	end ++
	  begin
	    hov 0 (str "proof." ++ fnl () ++
		     print_decl_script print_prf
		     ~nochange sigma (List.hd script))
	  end ++ fnl () ++
	  begin
	    if opened then mt () else (str "end proof." ++ fnl ())
	  end
    | Some(Daimon,spfl) ->
	((if nochange then (mt ()) else (pr_change sigma pf.goal ++ fnl ())) ++
	   prlist_with_sep pr_fnl print_prf spfl )
    | Some(rule,spfl) ->
	((if nochange then (mt ()) else (pr_change sigma pf.goal ++ fnl ())) ++
	   pr_rule_dot_fnl rule ++
	   prlist_with_sep pr_fnl print_prf spfl ) in
  print_prf pf

(* printed by Show Script command *)

let print_treescript ?(nochange=true) sigma pf =
  let rec print_prf pf =
    match pf.ref with
    | None ->
        if nochange then
	  str"<Your Proof Text here>"
	else pr_change sigma pf.goal
    | Some(Decl_proof opened,script) ->
	assert (List.length script = 1);
	begin
	  if nochange then mt () else pr_change sigma pf.goal ++ fnl ()
	end ++
	hov 0
	  begin str "proof." ++ fnl () ++
	    print_decl_script print_prf ~nochange sigma (List.hd script)
	  end ++ fnl () ++
	begin
	  if opened then mt () else (str "end proof." ++ fnl ())
	end
    | Some(Daimon,spfl) ->
	(if nochange then mt () else pr_change sigma pf.goal ++ fnl ()) ++
	prlist_with_sep pr_fnl (print_script ~nochange sigma) spfl
    | Some(r,spfl) ->
        let indent = if List.length spfl >= 2 then 1 else 0 in
        (if nochange then mt () else pr_change sigma pf.goal ++ fnl ()) ++
        hv indent (pr_rule_dot_fnl r ++ prlist_with_sep fnl print_prf spfl)
  in hov 0 (print_prf pf)

let rec print_info_script sigma osign pf =
  let sign = Goal.V82.hyps sigma pf.goal in
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

let format_print_info_script sigma osign pf =
  hov 0 (print_info_script sigma osign pf)


