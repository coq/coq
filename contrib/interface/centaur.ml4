(*i camlp4deps: "parsing/grammar.cma" i*)

(*Toplevel loop for the communication between Coq and Centaur *)
open Names;;
open Nameops;;
open Util;;
open Ast;;
open Term;;
open Pp;;
open Libobject;;
open Library;;
open Vernacinterp;;
open Evd;;
open Proof_trees;;
open Termast;;
open Tacmach;;
open Pfedit;;
open Proof_type;;
open Parsing;;
open Environ;;
open Declare;;
open Declarations;;
open Rawterm;;
open Reduction;;
open Classops;;
open Vernacinterp;;
open Vernac;;
open Command;;
open Protectedtoplevel;;
open Coqast;;
open Line_oriented_parser;;
open Xlate;;
open Vtp;;
open Ascent;;
open Translate;;
open Name_to_ast;;
open Pbp;;
open Blast;;
open Dad;;
open Debug_tac;;
open Search;;
open Astterm;;
open Nametab;;
open Showproof;;
open Showproof_ct;;
open Tacexpr;;
open Vernacexpr;;

let pcoq_started = ref None;;

let if_pcoq f a =
  if !pcoq_started <> None then f a else error "Pcoq is not started";;

let text_proof_flag = ref "en";;

(* 
let current_proof_name = ref "";;
*)
let current_proof_name () = string_of_id (get_current_proof_name ())

let current_goal_index = ref 0;;

set_flags := (function () ->
                if List.mem "G_natsyntax" (Mltop.get_loaded_modules()) then
                  (g_nat_syntax_flag := true; ())
                else ());;

let guarded_force_eval_stream (s : std_ppcmds) = 
  let l = ref [] in
  let f elt = l:= elt :: !l in 
  (try  Stream.iter f s with
  | _ -> f (Stream.next (str "error guarded_force_eval_stream")));
  Stream.of_list (List.rev !l);;


let rec string_of_path p =
    match p with [] -> "\n"
              | i::p -> (string_of_int i)^" "^ (string_of_path p)
;;
let print_path p =
    output_results_nl (str "Path:" ++ str  (string_of_path p))
;;

let kill_proof_node index =
 let paths = History.historical_undo (current_proof_name()) index in
 let _ =  List.iter
            (fun path -> (traverse_to path;
                          Pfedit.mutate weak_undo_pftreestate;
			  traverse_to []))
          paths in
 History.border_length (current_proof_name());;


(*Message functions, the text of these messages is recognized by the protocols *)
(*of CtCoq                                                                     *)
let ctf_header message_name request_id =
 fnl () ++ str "message" ++ fnl() ++ str message_name ++ fnl() ++
 int request_id ++ fnl();;

let ctf_acknowledge_command request_id command_count opt_exn =
  let goal_count, goal_index = 
    if refining() then
      let g_count =
        List.length 
          (fst (frontier (proof_of_pftreestate (get_pftreestate ())))) in
        g_count, (min g_count !current_goal_index)
    else
      (0, 0) in
   (ctf_header "acknowledge" request_id ++
    int command_count ++ fnl() ++
    int goal_count ++ fnl () ++
    int goal_index ++ fnl () ++
    str (current_proof_name()) ++ fnl() ++
    (match opt_exn with
      Some e -> Cerrors.explain_exn e
    | None -> mt ()) ++ fnl() ++ str "E-n-d---M-e-s-s-a-g-e" ++ fnl ());;

let ctf_undoResults = ctf_header "undo_results";;

let ctf_TextMessage = ctf_header "text_proof";;

let ctf_SearchResults = ctf_header "search_results";;

let ctf_OtherGoal = ctf_header "other_goal";;

let ctf_Location = ctf_header "location";;

let ctf_StateMessage = ctf_header "state";;

let ctf_PathGoalMessage () =
 fnl () ++ str "message" ++ fnl () ++ str "single_goal" ++ fnl ();;

let ctf_GoalReqIdMessage = ctf_header "single_goal_state";;

let ctf_NewStateMessage = ctf_header "fresh_state";;

let ctf_SavedMessage () = fnl () ++ str "message" ++ fnl () ++
			  str "saved" ++ fnl();;

let ctf_KilledMessage req_id ngoals =
 ctf_header "killed" req_id ++ int ngoals ++ fnl ();;

let ctf_AbortedAllMessage () =
  fnl() ++ str "message" ++ fnl() ++ str "aborted_all" ++ fnl();;

let ctf_AbortedMessage request_id na =
  ctf_header "aborted_proof" request_id ++ str na ++ fnl () ++ 
  str "E-n-d---M-e-s-s-a-g-e" ++ fnl ();;

let ctf_UserErrorMessage request_id stream =
 let stream = guarded_force_eval_stream stream in
 ctf_header "user_error" request_id ++ stream ++ fnl() ++
 str "E-n-d---M-e-s-s-a-g-e" ++ fnl();;

let ctf_ResetInitialMessage () =
 fnl () ++ str "message" ++ fnl () ++ str "reset_initial" ++ fnl ();;

let ctf_ResetIdentMessage request_id s =
 ctf_header "reset_ident" request_id ++ str s ++ fnl () ++
  str  "E-n-d---M-e-s-s-a-g-e" ++ fnl();;

type vtp_tree =
  | P_rl of ct_RULE_LIST
  | P_r of ct_RULE
  | P_s_int of ct_SIGNED_INT_LIST
  | P_pl of ct_PREMISES_LIST
  | P_cl of ct_COMMAND_LIST
  | P_t of ct_TACTIC_COM
  | P_text of ct_TEXT
  | P_ids of ct_ID_LIST;;

let print_tree t = 
  (match t with
  | P_rl x -> fRULE_LIST x
  | P_r x -> fRULE x
  | P_s_int x -> fSIGNED_INT_LIST x
  | P_pl x -> fPREMISES_LIST x
  | P_cl x -> fCOMMAND_LIST x
  | P_t x -> fTACTIC_COM x
  | P_text x -> fTEXT x
  | P_ids x -> fID_LIST x);
  print_string "e\nblabla\n";;



let break_happened = ref false;;

let output_results stream vtp_tree =
    let _ = Sys.signal Sys.sigint
       (Sys.Signal_handle(fun i -> (break_happened := true;()))) in
    msg stream;
    match vtp_tree with
      Some t -> print_tree t
    | None -> ();;

let output_results_nl stream =
    let _ = Sys.signal Sys.sigint
       (Sys.Signal_handle(fun i -> break_happened := true;()))
    in
    msgnl stream;;


let rearm_break () =
    let _ = Sys.signal Sys.sigint (Sys.Signal_handle(fun i -> raise Sys.Break))
    in ();;

let check_break () =
   if (!break_happened) then
    begin
      break_happened := false;
      raise Sys.Break
    end
   else ();;

let print_past_goal index =
 let path = History.get_path_for_rank (current_proof_name()) index in
 try traverse_to path;
     let pf = proof_of_pftreestate (get_pftreestate ()) in
     output_results  (ctf_PathGoalMessage ())
       (Some (P_r (translate_goal pf.goal)))
 with
   | Invalid_argument s ->
      ((try traverse_to [] with _ -> ());
       error "No focused proof (No proof-editing in progress)")
   | e -> (try traverse_to [] with _ -> ()); raise e
;;

let show_nth n =
  try
    let pf = proof_of_pftreestate (get_pftreestate()) in
    if (!text_proof_flag<>"off") then
       (if n=0
	   then output_results (ctf_TextMessage !global_request_id)
                               (Some (P_text (show_proof !text_proof_flag [])))
           else			       
	   let path = History.get_nth_open_path (current_proof_name()) n in
	   output_results (ctf_TextMessage !global_request_id)
                          (Some (P_text (show_proof !text_proof_flag path))))
    else
      output_results (ctf_GoalReqIdMessage !global_request_id)
      (let goal = List.nth (fst (frontier pf))
                   (n - 1) in
      (Some (P_r (translate_goal goal))))
  with
  | Invalid_argument s -> 
       error "No focused proof (No proof-editing in progress)";;

(* The rest of the file contains commands that are changed from the plain
   Coq distribution *)

let ctv_SEARCH_LIST = ref ([] : ct_PREMISE list);;

(*
let filter_by_module_from_varg_list l =
  let dir_list, b = Vernacentries.interp_search_restriction l in
    Search.filter_by_module_from_list (dir_list, b);;
*)

let add_search (global_reference:global_reference) assumptions cstr =
  try 
    let env = Global.env() in
  let id_string =
    string_of_qualid (Nametab.shortest_qualid_of_global env 
			global_reference) in
  let ast = 
    try
      CT_premise (CT_ident id_string, translate_constr false assumptions cstr)
    with Not_found ->
      CT_premise (CT_ident id_string,
                  CT_coerce_ID_to_FORMULA(
                    CT_ident ("Error printing" ^ id_string))) in
    ctv_SEARCH_LIST:= ast::!ctv_SEARCH_LIST
  with e -> msgnl (str "add_search raised an exception"); raise e;;

(*
let make_error_stream node_string =
  str "The syntax of " ++ str node_string ++
  str " is inconsistent with the vernac interpreter entry";;
*)

let ctf_EmptyGoalMessage id =
  fnl () ++ str "Empty Goal is a no-op.  Fun oh fun." ++ fnl ();;


let print_check judg =
 let {uj_val=value; uj_type=typ} = judg in
 let value_ct_ast = 
     (try translate_constr false (Global.env()) value 
      with UserError(f,str) ->
           raise(UserError(f,
			   Ast.print_ast 
				(ast_of_constr true (Global.env()) value) ++
			      fnl () ++ str ))) in
 let type_ct_ast =
     (try translate_constr false (Global.env()) typ
      with UserError(f,str) ->
           raise(UserError(f, Ast.print_ast (ast_of_constr true (Global.env())
					       value) ++ fnl() ++ str))) in
 ((ctf_SearchResults !global_request_id),
 (Some  (P_pl
  (CT_premises_list
  [CT_coerce_TYPED_FORMULA_to_PREMISE
    (CT_typed_formula(value_ct_ast,type_ct_ast)
    )]))));;

let ct_print_eval ast red_fun env judg =
((if refining() then traverse_to []);
let {uj_val=value; uj_type=typ} = judg in
let nvalue = red_fun value
(* // Attention , ici il faut peut être utiliser des environnemenst locaux *)
and ntyp = nf_betaiota typ in
(ctf_SearchResults !global_request_id,
 Some (P_pl
  (CT_premises_list
  [CT_eval_result
    (xlate_formula ast,
    translate_constr false env nvalue,
    translate_constr false env ntyp)]))));;



(* The following function is copied from globpr in env/printer.ml *)
let globcv x =
  let env = Global.env() in 
    match x with
      | Node(_,"MUTIND", (Path(_,sp))::(Num(_,tyi))::_) ->
	  let env = Global.env() in
	    convert_qualid
	      (Nametab.shortest_qualid_of_global env (IndRef(sp,tyi)))
      | Node(_,"MUTCONSTRUCT",(Path(_,sp))::(Num(_,tyi))::(Num(_,i))::_) ->
	  convert_qualid
            (Nametab.shortest_qualid_of_global env
	       (ConstructRef ((sp, tyi), i)))
  | _ -> failwith "globcv : unexpected value";;

let pbp_tac_pcoq =
    pbp_tac (function (x:raw_tactic_expr) -> 
      output_results
        (ctf_header "pbp_results" !global_request_id)
       (Some (P_t(xlate_tactic x))));;

let blast_tac_pcoq =
    blast_tac (function (x:raw_tactic_expr) -> 
      output_results
	(ctf_header "pbp_results" !global_request_id)
       (Some (P_t(xlate_tactic x))));;


let dad_tac_pcoq =
  dad_tac(function x -> 
    output_results
    (ctf_header "pbp_results" !global_request_id)
    (Some (P_t(xlate_tactic x))));;

let search_output_results () =
  output_results
       (ctf_SearchResults !global_request_id)
       (Some (P_pl (CT_premises_list
                      (List.rev !ctv_SEARCH_LIST))));;


let debug_tac2_pcoq tac =
      (fun g ->
	let the_goal = ref (None : goal sigma option) in
	let the_ast = ref tac in
	let the_path = ref ([] : int list) in
	try
	  let result = report_error tac the_goal the_ast the_path [] g in
	  (errorlabstrm "DEBUG TACTIC"
	     (str "no error here " ++ fnl () ++ pr_goal (sig_it g) ++
	      fnl () ++ str "the tactic is" ++ fnl () ++
	      Pptactic.pr_raw_tactic tac);
	   result)
	with
	  e ->
	    match !the_goal with
	      None -> raise e
	    | Some g -> 
                (output_results
		   (ctf_Location !global_request_id)
		   (Some (P_s_int
			    (CT_signed_int_list
                               (List.map
                                  (fun n -> CT_coerce_INT_to_SIGNED_INT
                                                 (CT_int n))
                                  (clean_path tac 
					       (List.rev !the_path)))))));
	    	(output_results
		   (ctf_OtherGoal !global_request_id)
		   (Some (P_r (translate_goal (sig_it g)))));
	    raise e);;

let rec selectinspect n env =
    match env with
      [] -> []
    | a::tl ->
      if n = 0 then
         []
      else
         match a with
           (sp, Lib.Leaf lobj) -> a::(selectinspect (n -1 ) tl)
         | _ -> (selectinspect n tl);;

open Term;;

let inspect n =
  let env = Global.env() in
  let add_search2 x y = add_search x env y in
  let l = selectinspect n (Lib.contents_after None) in
    ctv_SEARCH_LIST := [];
    List.iter
      (fun a ->
	 try
           (match a with
             	sp, Lib.Leaf lobj ->
		  (match sp, object_tag lobj with
                       _, "VARIABLE" ->
			 let ((_, _, v), _) = get_variable (basename sp) in
			   add_search2 (Nametab.locate (qualid_of_sp sp)) v
		     | sp, ("CONSTANT"|"PARAMETER") ->
			 let {const_type=typ} = Global.lookup_constant sp in
			   add_search2 (Nametab.locate (qualid_of_sp sp)) typ
		     | sp, "MUTUALINDUCTIVE" ->
			 add_search2 (Nametab.locate (qualid_of_sp sp))
			   (Pretyping.understand Evd.empty (Global.env())
			      (RRef(dummy_loc, IndRef(sp,0))))
		     | _ -> failwith ("unexpected value 1 for "^ 
				      (string_of_id (basename sp))))
              | _ -> failwith "unexpected value")
	 with e -> ())
      l;
    output_results
      (ctf_SearchResults !global_request_id)
      (Some
         (P_pl (CT_premises_list (List.rev !ctv_SEARCH_LIST))));;

let ct_int_to_TARG n = 
  CT_coerce_ID_OR_INT_to_TARG
    (CT_coerce_INT_to_ID_OR_INT (CT_int n));;

let pair_list_to_ct l =
    CT_user_tac(CT_ident "pair_int_list",
		CT_targ_list
		  (List.map (fun (a,b) ->
			       CT_coerce_TACTIC_COM_to_TARG
				 (CT_user_tac
				    (CT_ident "pair_int",
				     CT_targ_list
				       [ct_int_to_TARG a; ct_int_to_TARG b])))
		     l));;

(* Annule toutes les commandes qui s'appliquent sur les sous-buts du
   but auquel a été appliquée la n-ième tactique *)
let logical_kill n =
  let path = History.get_path_for_rank (current_proof_name()) n in
  begin
    traverse_to path;
    Pfedit.mutate weak_undo_pftreestate;
    (let kept_cmds, undone_cmds, remaining_goals, current_goal =
      History.logical_undo (current_proof_name()) n in
       output_results (ctf_undoResults !global_request_id)
	 (Some
	    (P_t
	       (CT_user_tac
		  (CT_ident "log_undo_result",
		   CT_targ_list
		     [CT_coerce_TACTIC_COM_to_TARG (pair_list_to_ct kept_cmds);
		      CT_coerce_TACTIC_COM_to_TARG(pair_list_to_ct undone_cmds);
		      ct_int_to_TARG remaining_goals;
		      ct_int_to_TARG current_goal])))));
    traverse_to []
  end;;

let simulate_solve n tac =
  let path = History.get_nth_open_path (current_proof_name()) n in
  solve_nth n (Tacinterp.hide_interp tac);
  traverse_to path;
  Pfedit.mutate weak_undo_pftreestate;
  traverse_to []

let kill_node_verbose n =
  let ngoals = kill_proof_node n in
  output_results_nl (ctf_KilledMessage !global_request_id ngoals)

let set_text_mode s = text_proof_flag := s

VERNAC ARGUMENT EXTEND text_mode
| [ "fr" ] -> [ "fr" ]
| [ "en" ] -> [ "en" ]
| [ "Off" ] -> [ "off" ]
END

VERNAC COMMAND EXTEND TextMode
| [ "Text" "Mode" text_mode(s) ] -> [ set_text_mode s ]
END

VERNAC COMMAND EXTEND OutputGoal
  [ "Goal" ] -> [ output_results_nl(ctf_EmptyGoalMessage "") ]
END

VERNAC COMMAND EXTEND OutputGoal
  [ "Goal" "Cmd" natural(n) "with" tactic(tac) ] -> [ simulate_solve n tac ]
END

VERNAC COMMAND EXTEND KillProofAfter
| [ "Kill" "Proof" "after"  natural(n) ] -> [ kill_node_verbose n ]
END

VERNAC COMMAND EXTEND KillProofAt
| [ "Kill" "Proof" "at"  natural(n) ] -> [ kill_node_verbose n ]
END

VERNAC COMMAND EXTEND KillSubProof
  [ "Kill" "SubProof" natural(n) ] -> [ logical_kill n ]
END

let start_proof_hook () =
  History.start_proof (current_proof_name());
  current_goal_index := 1

let solve_hook n =
  let name = current_proof_name () in
  let old_n_count = History.border_length name in
  let pf = proof_of_pftreestate (get_pftreestate ()) in
  let n_goals = (List.length (fst (frontier pf))) + 1 - old_n_count in
  begin
    current_goal_index := n;
    History.push_command name  n n_goals
  end

let abort_hook s = output_results_nl (ctf_AbortedMessage !global_request_id s)

let pcoq_search s l =
  ctv_SEARCH_LIST:=[];
  begin match s with
  | SearchPattern c ->
      let _,pat = interp_constrpattern Evd.empty (Global.env()) c in
      raw_pattern_search (filter_by_module_from_list l) add_search pat
  | SearchRewrite c ->
      let _,pat = interp_constrpattern Evd.empty (Global.env()) c in
      raw_search_rewrite (filter_by_module_from_list l) add_search pat;
  | SearchHead locqid ->
      filtered_search
	(filter_by_module_from_list l) add_search (Nametab.global locqid)
  end;
  search_output_results()

let pcoq_print_name (_,qid) =
  let results = xlate_vernac_list (name_to_ast qid) in
  output_results 
    (fnl () ++ str "message" ++ fnl () ++ str "PRINT_VALUE" ++ fnl ())
    (Some (P_cl results))

let pcoq_print_check j =
  let a,b = print_check j in output_results a b

let pcoq_print_eval redfun env c j =
  let strm, vtp = ct_print_eval (Ctast.ast_to_ct c) redfun env j in
  output_results strm vtp;;

open Vernacentries

let pcoq_show_goal = function
  | Some n -> show_nth n
  | None ->
      if !pcoq_started = Some true (* = debug *) then show_open_subgoals ()
      else errorlabstrm "show_goal"
	(str "Show must be followed by an integer in Centaur mode");;

let pcoq_hook = {
  start_proof = start_proof_hook;
  solve = solve_hook;
  abort = abort_hook;
  search = pcoq_search;
  print_name = pcoq_print_name;
  print_check = pcoq_print_check;
  print_eval = pcoq_print_eval;
  show_goal = pcoq_show_goal
}

(*
let command_changes = [
  ("TEXT_MODE",
   (function
     |  [Coqast.VARG_AST (Str(_,x))] ->
	 (fun () -> set_text_mode x)));

  ("StartProof", 
   (function
     | (Coqast.VARG_STRING kind) ::
       ((Coqast.VARG_IDENTIFIER s) ::
	((Coqast.VARG_CONSTR c) :: [])) ->
	  let stre =
	    match kind with
	    | "THEOREM" -> NeverDischarge
	    | "LEMMA" -> NeverDischarge
	    | "FACT" -> make_strength_1 ()
	    | "REMARK" -> make_strength_0 ()
	    | "DEFINITION" -> NeverDischarge
	    | "LET" -> make_strength_2 ()
	    | "LETTOP" -> NotDeclare
	    | "LOCAL" -> make_strength_0 ()
	    | _ -> errorlabstrm "StartProof" (make_error_stream "StartProof") in
	  fun () ->
	    begin
	      if kind = "LETTOP" && not(refining ()) then
		errorlabstrm "StartProof"
		  (str
		     "Let declarations can only be used in proof editing mode"
		  );
		let str = (string_of_id s) in
		start_proof_com (Some s) stre c;
		start_proof_hook str;
	    end
     | _ -> errorlabstrm "StartProof" (make_error_stream "StartProof")));

  ("GOAL", 
   (function
     | (Coqast.VARG_CONSTR c) :: [] ->
	 (fun () ->
	    if not (refining ()) then
	      begin
		start_proof_com None NeverDischarge c;
                start_proof_hook "Unnamed_thm"
	      end)
     | [] ->
	 (function () -> output_results_nl(ctf_EmptyGoalMessage ""))
     | _ -> errorlabstrm "Goal" (make_error_stream "Goal")));
  
  ("SOLVE",
   (function
     | [Coqast.VARG_NUMBER n; Coqast.VARG_TACTIC tcom] ->
       (fun () -> 
         if not (refining ()) then
           error "Unknown command of the non proof-editing mode";
         solve_nth n (Tacinterp.hide_interp tcom);
(* pcoq *)
         solve_hook n
(**)
     | _ -> errorlabstrm "SOLVE" (make_error_stream "SOLVE")));

(* SIMULE SOLVE SANS EFFET *)
  ("GOAL_CMD", 
   (function
     | (Coqast.VARG_NUMBER n) ::
       ((Coqast.VARG_TACTIC tac) :: []) ->
	 (function () -> 
	    let path = History.get_nth_open_path !current_proof_name n in
              solve_nth n (Tacinterp.hide_interp tac);
              traverse_to path;
              Pfedit.mutate weak_undo_pftreestate;
	      traverse_to [])
     | _ -> errorlabstrm "GOAL_CMD" (make_error_stream "GOAL_CMD")));

(* Revient à l'état avant l'application de la n-ième tactique *)
  ("KILL_NODE", 
   (function
     | (Coqast.VARG_NUMBER n) :: [] ->
	 (function () -> 
	   let ngoals = kill_proof_node n in
	   output_results_nl
             (ctf_KilledMessage !global_request_id ngoals))
     | _ -> errorlabstrm "KILL_NODE" (make_error_stream "KILL_NODE")));
(* Annule toutes les commandes qui s'appliquent sur les sous-buts du
   but auquel a été appliquée la n-ième tactique *)
  ("KILL_SUB_PROOF",
   (function
     | [Coqast.VARG_NUMBER n] ->
	 (function () -> logical_kill n)
     | _ -> errorlabstrm "KILL_SUB_PROOF" (make_error_stream "KILL_SUB_PROOF")));

  ("RESUME",
   (function [Coqast.VARG_IDENTIFIER id] ->
     (fun () -> 
       let str = (string_of_id id) in
	 resume_proof id;
(* Pcoq *)
	 current_proof_name := str)
(**)
      | _ -> errorlabstrm "RESUME" (make_error_stream "RESUME")));

(* NoOp... *)
  ("BeginSilent", 
   (function
     | [] ->
	 (function
	     () ->
	       errorlabstrm "Begin Silent" 
		 (str "not available in Centaur mode"))
     | _ -> errorlabstrm "BeginSilent" (make_error_stream "BeginSilent")));
  
  ("EndSilent", 
   (function
     | [] ->
	 (function
	     () ->
	       errorlabstrm "End Silent"
		 (str "not available in Centaur mode"))
     | _ -> errorlabstrm "EndSilent" (make_error_stream "EndSilent")));
  
  ("ABORT", 
   (function
     | (Coqast.VARG_IDENTIFIER id) :: [] ->
	 (function
	     () ->
	       delete_proof id;
(* Pcoq *)
	       current_proof_name := "";
	       output_results_nl
		 (ctf_AbortedMessage !global_request_id (string_of_id id)))
(**)
     | [] ->
	 (function
	     () -> delete_current_proof ();
(* Pcoq *)
	     current_proof_name := "";
	       output_results_nl
		 (ctf_AbortedMessage !global_request_id ""))
(**)
     | _ -> errorlabstrm "ABORT" (make_error_stream "ABORT")));
  ("SEARCH",
   function
       (Coqast.VARG_QUALID qid)::l ->
         (fun () -> 
           ctv_SEARCH_LIST:=[];
	    let global_ref = Nametab.global dummy_loc qid in
           filtered_search
             (filter_by_module_from_varg_list l)
	     add_search (Nametab.locate qid);
	   search_output_results())
     |	_ -> failwith "bad form of arguments");

  ("SearchRewrite",
   function
       (Coqast.VARG_CONSTR c)::l ->
	 (fun () -> 
            ctv_SEARCH_LIST:=[];
	    let _,pat = interp_constrpattern Evd.empty (Global.env()) c in
              raw_search_rewrite
             	(filter_by_module_from_varg_list l)
             	add_search pat;
              search_output_results())
     |	_ -> failwith "bad form of arguments");

  ("SearchPattern",
   function
       (Coqast.VARG_CONSTR c)::l ->
	 (fun () ->
	    ctv_SEARCH_LIST := [];
	    let _,pat = interp_constrpattern Evd.empty (Global.env()) c in
	      raw_pattern_search
             	(filter_by_module_from_varg_list l)
             	add_search pat;
	      search_output_results())
     |	_ -> failwith "bad form of arguments");
  
  ("PrintId",
   (function
      | [Coqast.VARG_QUALID qid] ->
	 (function () -> 
	   let results = xlate_vernac_list (Ctast.ast_to_ct (name_to_ast qid)) in
	   output_results 
	     (fnl () ++ str "message" ++ fnl () ++ str "PRINT_VALUE" ++ fnl ())
	     (Some (P_cl results)))
     | _ -> errorlabstrm "PrintId" (make_error_stream "PrintId")));
  
  ("Check", 
   (function
     | (Coqast.VARG_STRING kind) :: ((Coqast.VARG_CONSTR c) :: g) ->
	 let evmap, env =
	   Vernacentries.get_current_context_of_args g in
	 let f =
	   match kind with
	   | "CHECK" -> print_check
	   | "PRINTTYPE" ->
	       errorlabstrm "PrintType" (str "Not yet supported in CtCoq")
	   | _ -> errorlabstrm "CHECK" (make_error_stream "CHECK") in
	 (function () -> 
	   let a,b = f (c, judgment_of_rawconstr evmap env c) in
	   output_results a b)
     | _ -> errorlabstrm "CHECK" (make_error_stream "CHECK")));
  
  ("Eval",
   (function
     | Coqast.VARG_TACTIC_ARG(Redexp redexp):: Coqast.VARG_CONSTR c :: g ->
	 let evmap, env = Vernacentries.get_current_context_of_args g in
	 let redfun =
	   ct_print_eval (Ctast.ast_to_ct c) (Tacred.reduction_of_redexp redexp env evmap) env in
	 fun () -> 
	   let strm, vtp = redfun evmap (judgment_of_rawconstr evmap env c) in
	   output_results strm vtp
     | _ -> errorlabstrm "Eval" (make_error_stream "Eval")));
  
  ("Centaur_Reset", 
   (function
     | (Coqast.VARG_IDENTIFIER c) :: [] ->
	 if refining () then 
	   output_results (ctf_AbortedAllMessage ()) None;
	   current_proof_name := "";
	 (match string_of_id c with
	 | "CtCoqInitialState" ->
	     (function
		 () ->
		   current_proof_name := "";
		   Vernacentries.abort_refine Lib.reset_initial ();
		   output_results (ctf_ResetInitialMessage ()) None)
	 | _ ->
	     (function
		 () ->
		   current_proof_name := "";
		   Vernacentries.abort_refine Lib.reset_name c;
		   output_results
		     (ctf_ResetIdentMessage
			!global_request_id (string_of_id c)) None))
     | _ -> errorlabstrm "Centaur_Reset" (make_error_stream "Centaur_Reset")));
  ("Show_dad_rules",
   (function
     | [] ->
	 (fun () -> 
	   let results = dad_rule_names() in
	   output_results
	     (ctf_header "dad_rule_names" !global_request_id)
	     (Some (P_ids
		      (CT_id_list
			 (List.map (fun s -> CT_ident s) results)))))
     | _ ->
	 errorlabstrm
	   "Show_dad_rules" (make_error_stream "Show_dad_rules")));
  ("INSPECT",
   (function
     | [Coqast.VARG_NUMBER n] ->
         (function () -> inspect n)
     | _ -> errorlabstrm "INSPECT" (make_error_stream "INSPECT")))

];;
*)
(*
let non_debug_changes = [
  ("SHOW", 
   (function
     | [Coqast.VARG_NUMBER n] -> (function () -> show_nth n)
     | _ -> errorlabstrm "SHOW" (make_error_stream "SHOW")))];;
*)

(* Moved to Vernacentries...
let command_creations = [
  ("Comments",
   function l -> (fun () -> message ("Comments ok\n")));
(* Dead code
  ("CommentsBold",
   function l -> (fun () -> message ("CommentsBold ok\n")));
  ("Title",
   function l -> (fun () -> message ("Title ok\n")));
  ("Author",
   function l -> (fun () -> message ("Author ok\n")));
  ("Note",
   function l -> (fun () -> message ("Note ok\n")));
  ("NL",
   function l -> (fun () -> message ("Newline ok\n")))
*)
];;
*)

TACTIC EXTEND Pbp
| [ "Pbp" ident_opt(idopt) natural_list(nl) ] -> 
    [ if_pcoq pbp_tac_pcoq idopt nl ]
END
TACTIC EXTEND Blast
| [ "Blast" ne_natural_list(nl) ] ->
    [ if_pcoq blast_tac_pcoq nl ]
END
TACTIC EXTEND Dad
| [ "Dad" natural_list(nl1) "to" natural_list(nl2) ] ->
    [ if_pcoq dad_tac_pcoq nl1 nl2 ]
END

TACTIC EXTEND CtDebugTac
| [ "DebugTac" tactic(t) ] -> [ if_pcoq debug_tac2_pcoq t ]
END

TACTIC EXTEND CtDebugTac2
| [ "DebugTac2" tactic(t) ] -> [ if_pcoq debug_tac2_pcoq t ]
END


let start_pcoq_mode debug = 
  begin
    pcoq_started := Some debug;
    start_dad();
    set_xlate_mut_stuff (fun x ->Ctast.ast_to_ct (globcv (Ctast.ct_to_ast x)));
    declare_in_coq();
(*
    add_tactic "PcoqPbp" pbp_tac_pcoq;
    add_tactic "PcoqBlast" blast_tac_pcoq;
    add_tactic "Dad" dad_tac_pcoq;
    add_tactic "CtDebugTac" debug_tac2_pcoq;
    add_tactic "CtDebugTac2" debug_tac2_pcoq;
*)
(* The following ones are added to enable rich comments in pcoq *)
(* TODO ...
    add_tactic "Image" (fun _ -> tclIDTAC);
*)
(* "Comments" moved to Vernacentries, other obsolete ?
    List.iter (fun (a,b) -> vinterp_add a b) command_creations;
*)
(* Now hooks in Vernacentries
    List.iter (fun (a,b) -> overwriting_vinterp_add a b) command_changes;
    if not debug then
      List.iter (fun (a,b) -> overwriting_vinterp_add a b) non_debug_changes;
*)
    set_pcoq_hook pcoq_hook;
  end;;

(*
vinterp_add "START_PCOQ"
            (function _ -> 
              (function () ->
                start_pcoq_mode false;
		set_acknowledge_command ctf_acknowledge_command;
                set_start_marker "CENTAUR_RESERVED_TOKEN_start_command";
                set_end_marker "CENTAUR_RESERVED_TOKEN_end_command";
                raise Vernacinterp.ProtectedLoop));;

vinterp_add "START_PCOQ_DEBUG"
            (function _ -> 
              (function () ->
                start_pcoq_mode true;
		set_acknowledge_command ctf_acknowledge_command;
                set_start_marker "--->";
                set_end_marker "<---";
                raise Vernacinterp.ProtectedLoop));;
*)
let start_pcoq () =
  start_pcoq_mode false;
  set_acknowledge_command ctf_acknowledge_command;
  set_start_marker "CENTAUR_RESERVED_TOKEN_start_command";
  set_end_marker "CENTAUR_RESERVED_TOKEN_end_command"(*;
  raise Vernacexpr.ProtectedLoop*)

let start_pcoq_debug () =
  start_pcoq_mode true;
  set_acknowledge_command ctf_acknowledge_command;
  set_start_marker "--->";
  set_end_marker "<---"(*;
  raise Vernacexpr.ProtectedLoop;;*)

VERNAC COMMAND EXTEND StartPcoq
  [ "Start" "Pcoq" "Mode" ] -> [ start_pcoq () ]
END

VERNAC COMMAND EXTEND StartPcoqDebug
| [ "Start" "Pcoq" "Debug" "Mode" ] -> [ start_pcoq_debug () ]
END
