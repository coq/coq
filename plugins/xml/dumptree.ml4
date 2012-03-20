(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module provides the "Dump Tree" command that allows dumping the
    current state of the proof stree in XML format *)

(** Contributed by Cezary Kaliszyk, Radboud University Nijmegen *)

(*i camlp4deps: "parsing/grammar.cma" i*)
open Tacexpr;;
open Decl_mode;;
open Printer;;
open Pp;;
open Environ;;
open Format;;
open Proof_type;;
open Evd;;
open Termops;;
open Ppconstr;;
open Names;;

exception Different

let xmlstream s =
  (* In XML we want to print the whole stream so we can force the evaluation *)
  Stream.of_list (List.map xmlescape (Stream.npeek max_int s))
;;

let thin_sign osign sign =
  Sign.fold_named_context
    (fun (id,c,ty as d) sign ->
       try
        if Sign.lookup_named id osign = (id,c,ty) then sign
         else raise Different
       with Not_found | Different -> Environ.push_named_context_val d sign)
    sign ~init:Environ.empty_named_context_val
;;

let pr_tactic_xml = function
  | TacArg (_,Tacexp t) -> str "<tactic cmd=\"" ++ xmlstream (Pptactic.pr_glob_tactic (Global.env()) t) ++ str "\"/>"
  | t -> str "<tactic cmd=\"" ++ xmlstream (Pptactic.pr_tactic (Global.env()) t) ++ str "\"/>"
;;

let pr_proof_instr_xml instr =
  Ppdecl_proof.pr_proof_instr (Global.env()) instr
;;

let pr_rule_xml pr = function
  | Prim r -> str "<rule text=\"" ++ xmlstream (pr_prim_rule r) ++ str "\"/>"
  | Nested(cmpd, subtree) ->
      hov 2 (str "<cmpdrule>" ++ fnl () ++
        begin match cmpd with
          Tactic (texp, _) -> pr_tactic_xml texp
        end ++ fnl ()
        ++ pr subtree
      ) ++ fnl () ++ str "</cmpdrule>"
  | Daimon -> str "<daimon/>"
  | Decl_proof _ -> str "<proof/>"
;;

let pr_var_decl_xml env (id,c,typ) =
  let ptyp = print_constr_env env typ in
  match c with
  | None ->
      (str "<hyp id=\"" ++ xmlstream (pr_id id) ++ str "\" type=\"" ++ xmlstream ptyp ++ str "\"/>")
  | Some c ->
      (* Force evaluation *)
      let pb = print_constr_env env c in
      (str "<hyp id=\"" ++ xmlstream (pr_id id) ++ str "\" type=\"" ++ xmlstream ptyp ++ str "\" body=\"" ++
         xmlstream pb ++ str "\"/>")
;;

let pr_rel_decl_xml env (na,c,typ) =
  let pbody = match c with
    | None -> mt ()
    | Some c ->
	(* Force evaluation *)
	let pb = print_constr_env env c in
	  (str" body=\"" ++ xmlstream pb ++ str "\"") in
  let ptyp = print_constr_env env typ in
  let pid =
    match na with
    | Anonymous -> mt ()
    | Name id -> str " id=\"" ++ pr_id id ++ str "\""
  in
  (str "<hyp" ++ pid ++ str " type=\"" ++ xmlstream ptyp ++ str "\"" ++ pbody ++ str "/>")
;;

let pr_context_xml env =
  let sign_env =
    fold_named_context
      (fun env d pp -> pp ++ pr_var_decl_xml env d)
      env ~init:(mt ())
  in
  let db_env =
    fold_rel_context
      (fun env d pp -> pp ++ pr_rel_decl_xml env d)
      env ~init:(mt ())
  in
  (sign_env ++ db_env)
;;

let pr_subgoal_metas_xml metas env=
  let pr_one (meta, typ) =
    fnl () ++ str "<meta index=\"" ++ int meta ++ str " type=\"" ++ xmlstream (pr_goal_concl_style_env env typ) ++
      str "\"/>"
  in
  List.fold_left (++) (mt ()) (List.map pr_one metas)
;;

let pr_goal_xml sigma g =
  let env = try Goal.V82.unfiltered_env sigma g with _ -> empty_env in
  if Decl_mode.try_get_info sigma g = None then
    (hov 2 (str "<goal>" ++ fnl () ++ str "<concl type=\"" ++
    xmlstream (pr_goal_concl_style_env env (Goal.V82.concl sigma g)) ++
    str "\"/>" ++
    (pr_context_xml env)) ++
    fnl () ++ str "</goal>")
  else
    (hov 2 (str "<goal type=\"declarative\">" ++
    (pr_context_xml env)) ++
    fnl () ++ str "</goal>")
;;

let print_proof_xml () =
  Errors.anomaly "Dump Tree command not supported in this version."


VERNAC COMMAND EXTEND DumpTree
  [ "Dump" "Tree" ] -> [ print_proof_xml () ]
END
