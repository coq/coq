(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *   The HELM Project         /   The EU MoWGLI Project       *)
(*         *   University of Bologna                                    *)
(************************************************************************)
(*          This file is distributed under the terms of the             *)
(*           GNU Lesser General Public License Version 2.1              *)
(*                                                                      *)
(*                 Copyright (C) 2000-2004, HELM Team.                  *)
(*                       http://helm.cs.unibo.it                        *)
(************************************************************************)

let prooftreedtdname = "http://mowgli.cs.unibo.it/dtd/prooftree.dtd";;

let std_ppcmds_to_string s =
   Pp.msg_with Format.str_formatter s;
   Format.flush_str_formatter ()
;;

let idref_of_id id = "v" ^ id;;

(* Transform a constr to an Xml.token Stream.t *)
(* env is a named context                      *)
(*CSC: in verita' dovrei "separare" le variabili vere e lasciarle come Var! *)
let constr_to_xml obj sigma env =
  let ids_to_terms = Hashtbl.create 503 in
  let constr_to_ids = Acic.CicHash.create 503 in
  let ids_to_father_ids = Hashtbl.create 503 in
  let ids_to_inner_sorts = Hashtbl.create 503 in
  let ids_to_inner_types = Hashtbl.create 503 in

  (* named_context holds section variables and local variables *)
  let named_context = Environ.named_context env  in
  (* real_named_context holds only the section variables *)
  let real_named_context = Environ.named_context (Global.env ()) in
  (* named_context' holds only the local variables *)
  let named_context' =
   List.filter (function n -> not (List.mem n real_named_context)) named_context
  in
  let idrefs =
   List.map
    (function x,_,_ -> idref_of_id (Names.string_of_id x)) named_context' in
  let rel_context = Sign.push_named_to_rel_context named_context' [] in
  let rel_env =
   Environ.push_rel_context rel_context
    (Environ.reset_with_named_context
	(Environ.val_of_named_context real_named_context) env) in
  let obj' =
   Term.subst_vars (List.map (function (i,_,_) -> i) named_context') obj in
  let seed = ref 0 in
   try
    let annobj =
     Cic2acic.acic_of_cic_context' false seed ids_to_terms constr_to_ids
      ids_to_father_ids ids_to_inner_sorts ids_to_inner_types rel_env
      idrefs sigma (Unshare.unshare obj') None
    in
     Acic2Xml.print_term ids_to_inner_sorts annobj
   with e ->
    Util.anomaly
     ("Problem during the conversion of constr into XML: " ^
      Printexc.to_string e)
(* CSC: debugging stuff
Pp.ppnl (Pp.str "Problem during the conversion of constr into XML") ;
Pp.ppnl (Pp.str "ENVIRONMENT:") ;
Pp.ppnl (Printer.pr_context_of rel_env) ;
Pp.ppnl (Pp.str "TERM:") ;
Pp.ppnl (Printer.pr_lconstr_env rel_env obj') ;
Pp.ppnl (Pp.str "RAW-TERM:") ;
Pp.ppnl (Printer.pr_lconstr obj') ;
Xml.xml_empty "MISSING TERM" [] (*; raise e*)
*)
;;

let first_word s =
   try let i = String.index s ' ' in
       String.sub s 0 i
   with _ -> s
;;

let string_of_prim_rule x = match x with
  | Proof_type.Intro _-> "Intro"
  | Proof_type.Cut _ -> "Cut"
  | Proof_type.FixRule _ -> "FixRule"
  | Proof_type.Cofix _ -> "Cofix"
  | Proof_type.Refine _ -> "Refine"
  | Proof_type.Convert_concl _ -> "Convert_concl"
  | Proof_type.Convert_hyp _->"Convert_hyp"
  | Proof_type.Thin _ -> "Thin"
  | Proof_type.ThinBody _-> "ThinBody"
  | Proof_type.Move (_,_,_) -> "Move"
  | Proof_type.Order _ -> "Order"
  | Proof_type.Rename (_,_) -> "Rename"
  | Proof_type.Change_evars -> "Change_evars"

let
 print_proof_tree curi sigma pf proof_tree_to_constr
  proof_tree_to_flattened_proof_tree constr_to_ids
=
 let module PT = Proof_type in
 let module L = Logic in
 let module X = Xml in
 let module T = Tacexpr in
  let ids_of_node node =
   let constr = Proof2aproof.ProofTreeHash.find proof_tree_to_constr node in
(*
let constr =
 try
    Proof2aproof.ProofTreeHash.find proof_tree_to_constr node
 with _ -> Pp.ppnl (Pp.(++) (Pp.str "Node of the proof-tree that generated
no lambda-term: ") (Refiner.print_script true (Evd.empty)
(Global.named_context ()) node)) ; assert false (* Closed bug, should not
happen any more *)
in
*)
   try
    Some (Acic.CicHash.find constr_to_ids constr)
   with _ ->
Pp.ppnl (Pp.(++) (Pp.str
"The_generated_term_is_not_a_subterm_of_the_final_lambda_term")
(Printer.pr_lconstr constr)) ;
    None
  in
  let rec aux node old_hyps =
   let of_attribute =
    match ids_of_node node with
       None -> []
     | Some id -> ["of",id]
   in
    match node with
       {PT.ref=Some(PT.Prim tactic_expr,nodes)} ->
         let tac = string_of_prim_rule tactic_expr in
         let of_attribute = ("name",tac)::of_attribute in
          if nodes = [] then
           X.xml_empty "Prim" of_attribute
          else
           X.xml_nempty "Prim" of_attribute
            (List.fold_left
              (fun i n -> [< i ; (aux n old_hyps) >]) [<>] nodes)

     | {PT.goal=goal;
        PT.ref=Some(PT.Nested (PT.Tactic(tactic_expr,_),hidden_proof),nodes)} ->
         (* [hidden_proof] is the proof of the tactic;                     *)
         (* [nodes] are the proof of the subgoals generated by the tactic; *)
         (* [flat_proof] if the proof-tree obtained substituting [nodes]   *)
         (*  for the holes in [hidden_proof]                               *)
        let flat_proof =
         Proof2aproof.ProofTreeHash.find proof_tree_to_flattened_proof_tree node
        in begin
        match tactic_expr with
        | T.TacArg (T.Tacexp _) ->
            (* We don't need to keep the level of abstraction introduced at *)
            (* user-level invocation of tactic... (see Tacinterp.hide_interp)*)
            aux flat_proof old_hyps
        | _ ->
         (****** la tactique employee *)
	 let prtac = Pptactic.pr_tactic (Global.env()) in
         let tac = std_ppcmds_to_string (prtac tactic_expr) in
         let tacname= first_word tac in
         let of_attribute = ("name",tacname)::("script",tac)::of_attribute in

         (****** le but *)
         let {Evd.evar_concl=concl;
              Evd.evar_hyps=hyps}=goal in

         let env = Global.env_of_context hyps in

         let xgoal =
          X.xml_nempty "Goal" [] (constr_to_xml concl sigma env) in

         let rec build_hyps =
          function
           | [] -> xgoal
           | (id,c,tid)::hyps1 ->
              let id' = Names.string_of_id id in
               [< build_hyps hyps1;
                  (X.xml_nempty "Hypothesis"
                    ["id",idref_of_id id' ; "name",id']
                    (constr_to_xml tid sigma env))
               >] in
         let old_names = List.map (fun (id,c,tid)->id) old_hyps in
	 let nhyps = Environ.named_context_of_val hyps in
         let new_hyps =
          List.filter (fun (id,c,tid)-> not (List.mem id old_names)) nhyps in

         X.xml_nempty "Tactic" of_attribute
          [<(build_hyps new_hyps) ; (aux flat_proof nhyps)>]
        end

     | {PT.ref=Some((PT.Nested(PT.Proof_instr (_,_),_)|PT.Decl_proof _),nodes)} ->
         Util.anomaly "Not Implemented"

     | {PT.ref=Some(PT.Daimon,_)} ->
         X.xml_empty "Hidden_open_goal" of_attribute

     | {PT.ref=None;PT.goal=goal} ->
         X.xml_empty "Open_goal" of_attribute
  in
   [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
      X.xml_cdata ("<!DOCTYPE ProofTree SYSTEM \""^prooftreedtdname ^"\">\n\n");
      X.xml_nempty "ProofTree" ["of",curi] (aux pf [])
   >]
;;


(* Hook registration *)
(* CSC: debranched since it is bugged
Xmlcommand.set_print_proof_tree print_proof_tree;;
*)
