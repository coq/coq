
(*Toplevel loop for the communication between Coq and Centaur *)
open Names;;
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
open Dad;;
open Debug_tac;;
open Search;;
open Astterm;;
open Nametab;;


let text_proof_flag = ref false;;

let current_proof_name = ref "";;

let current_goal_index = ref 0;;

set_flags := (function () ->
                if List.mem "G_natsyntax" (Mltop.get_loaded_modules()) then
                  (g_nat_syntax_flag := true; ())
                else ());;

let guarded_force_eval_stream s = 
  let l = ref [] in
  let f elt = l:= elt :: !l in 
  (try  Stream.iter f s with
  | _ -> f (sTR "error guarded_force_eval_stream"));
  Stream.of_list (List.rev !l);;


let rec string_of_path p =
    match p with [] -> "\n"
              | i::p -> (string_of_int i)^" "^ (string_of_path p)
;;
let print_path p =
    output_results_nl [< 'sTR "Path:"; 'sTR  (string_of_path p)>]
;;

let kill_proof_node index =
 let paths = History.historical_undo !current_proof_name index in
 let _ =  List.iter
            (fun path -> (traverse_to path;
                          Pfedit.mutate weak_undo_pftreestate;
			  traverse_to []))
          paths in
 History.border_length !current_proof_name;;


(*Message functions, the text of these messages is recognized by the protocols *)
(*of CtCoq                                                                     *)
let ctf_header message_name request_id =
 [< 'fNL; 'sTR "message"; 'fNL; 'sTR message_name; 'fNL; 'iNT request_id; 'fNL >];;

let ctf_acknowledge_command request_id command_count opt_exn =
  let goal_count, goal_index = 
    if refining() then
      let g_count =
        List.length 
          (fst (frontier (proof_of_pftreestate (get_pftreestate ())))) in
        g_count, (min g_count !current_goal_index)
    else
      (0, 0) in
  [< ctf_header "acknowledge" request_id;
     'iNT command_count; 'fNL; 
    'iNT goal_count; 'fNL; 
    'iNT goal_index; 'fNL; 
    'sTR !current_proof_name; 'fNL;
    (match opt_exn with
      Some e -> Errors.explain_exn e
    | None -> [< >]); 'fNL; 'sTR "E-n-d---M-e-s-s-a-g-e"; 'fNL >];;

let ctf_undoResults = ctf_header "undo_results";;

let ctf_TextMessage = ctf_header "text_proof";;

let ctf_SearchResults = ctf_header "search_results";;

let ctf_OtherGoal = ctf_header "other_goal";;

let ctf_Location = ctf_header "location";;

let ctf_StateMessage = ctf_header "state";;

let ctf_PathGoalMessage () =
 [< 'fNL; 'sTR "message"; 'fNL; 'sTR "single_goal"; 'fNL >];;

let ctf_GoalReqIdMessage = ctf_header "single_goal_state";;

let ctf_NewStateMessage = ctf_header "fresh_state";;

let ctf_SavedMessage () = [< 'fNL; 'sTR "message"; 'fNL; 'sTR "saved"; 'fNL >];;

let ctf_KilledMessage req_id ngoals =
 [< ctf_header "killed" req_id; 'iNT ngoals; 'fNL >];;

let ctf_AbortedAllMessage () =
 [< 'fNL; 'sTR "message"; 'fNL; 'sTR "aborted_all"; 'fNL >];;

let ctf_AbortedMessage request_id na =
 [< 'fNL; 'sTR "message"; 'fNL; 'sTR "aborted_proof"; 'fNL; 'iNT request_id; 'fNL;
 'sTR na; 'fNL; 'sTR "E-n-d---M-e-s-s-a-g-e"; 'fNL >];;

let ctf_UserErrorMessage request_id stream =
 let stream = guarded_force_eval_stream stream in
 [< 'fNL; 'sTR "message"; 'fNL; 'sTR "user_error"; 'fNL; 'iNT request_id; 'fNL;
  stream; 'fNL; 'sTR "E-n-d---M-e-s-s-a-g-e"; 'fNL >];;

let ctf_ResetInitialMessage () =
 [< 'fNL; 'sTR "message"; 'fNL; 'sTR "reset_initial"; 'fNL >];;

let ctf_ResetIdentMessage request_id str =
 [< 'fNL; 'sTR "message"; 'fNL; 'sTR "reset_ident"; 'fNL; 'iNT request_id; 'fNL;
 'sTR str; 'fNL; 'sTR "E-n-d---M-e-s-s-a-g-e"; 'fNL >];;

type vtp_tree =
  | P_rl of ct_RULE_LIST
  | P_r of ct_RULE
  | P_s_int of ct_SIGNED_INT_LIST
  | P_pl of ct_PREMISES_LIST
  | P_cl of ct_COMMAND_LIST
  | P_t of ct_TACTIC_COM
  | P_ids of ct_ID_LIST;;

let print_tree t = 
  (match t with
  | P_rl x -> fRULE_LIST x
  | P_r x -> fRULE x
  | P_s_int x -> fSIGNED_INT_LIST x
  | P_pl x -> fPREMISES_LIST x
  | P_cl x -> fCOMMAND_LIST x
  | P_t x -> fTACTIC_COM x
  | P_ids x -> fID_LIST x);
  print_string "e\nblabla\n";;



let break_happened = ref false;;

let output_results stream vtp_tree =
    let _ = Sys.signal Sys.sigint
       (Sys.Signal_handle(fun i -> (break_happened := true;()))) in
    mSG stream;
    match vtp_tree with
      Some t -> print_tree t
    | None -> ();;

let output_results_nl stream =
    let _ = Sys.signal Sys.sigint
       (Sys.Signal_handle(fun i -> break_happened := true;()))
    in
    mSGNL stream;;


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
 let path = History.get_path_for_rank !current_proof_name index in
 try traverse_to path;
     let pf = proof_of_pftreestate (get_pftreestate ()) in
     output_results  (ctf_PathGoalMessage ())
       (Some (P_r (translate_goal pf.goal)))
 with
 | Invalid_argument s -> error "No focused proof (No proof-editing in progress)"
;;

let show_nth n =
  try
    let pf = proof_of_pftreestate (get_pftreestate()) in
    if (!text_proof_flag) then
      errorlabstrm "debug" [< 'sTR "text printing unplugged" >]
(*
       (if n=0
	   then output_results (ctf_TextMessage !global_request_id)
                               (Some (P_t (show_proof [])))
           else			       
	   let path = History.get_nth_open_path !current_proof_name n in
	   output_results (ctf_TextMessage !global_request_id)
                          (Some (P_t (show_proof path))))
*)
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

let filter_by_module_from_varg_list (l:vernac_arg list) =
  let dir_list, b = Vernacentries.inside_outside l in
    Search.filter_by_module_from_list (dir_list, b);;

let add_search (global_reference:global_reference) assumptions cstr =
  mSGNL [< 'sTR "DEBUG: entering add_search" >];
  try 
  let id_string = string_of_qualid (Global.qualid_of_global global_reference) in
  let _ = mSGNL [< 'sTR "DEBUG: " ; 'sTR id_string >] in
  let ast = 
    try
      CT_premise (CT_ident id_string, translate_constr assumptions cstr)
    with Not_found ->
      CT_premise (CT_ident id_string,
                  CT_coerce_ID_to_FORMULA(
                    CT_ident ("Error printing" ^ id_string))) in
    ctv_SEARCH_LIST:= ast::!ctv_SEARCH_LIST
  with e -> mSGNL [< 'sTR "add_search raised an exception" >]; raise e;;

let make_error_stream node_string =
 [< 'sTR "The syntax of "; 'sTR node_string;
 'sTR " is inconsistent with the vernac interpreter entry" >];;

let ctf_EmptyGoalMessage id =
 [< 'fNL; 'sTR "Empty Goal is a no-op.  Fun oh fun."; 'fNL >];;


let print_check (ast, judg) =
 let {uj_val=value; uj_type=typ} = judg in
 let value_ct_ast = 
     (try translate_constr (Global.env()) value 
      with UserError(f,str) ->
           raise(UserError(f,
			   [< Ast.print_ast 
				(ast_of_constr true (Global.env()) value);
			      'fNL; str >]))) in
 let type_ct_ast =
     (try translate_constr (Global.env()) typ
      with UserError(f,str) ->
           raise(UserError(f, [< Ast.print_ast (ast_of_constr true (Global.env())
					       value);
				 'fNL; str >]))) in
 ((ctf_SearchResults !global_request_id),
 (Some  (P_pl
  (CT_premises_list
  [CT_coerce_TYPED_FORMULA_to_PREMISE
    (CT_typed_formula(value_ct_ast,type_ct_ast)
    )]))));;

let ct_print_eval ast red_fun env evd judg =
((if refining() then traverse_to []);
let {uj_val=value; uj_type=typ} = judg in
let nvalue = red_fun value
(* // Attention , ici il faut peut être utiliser des environnemenst locaux *)
and ntyp = nf_betaiota env evd typ in
(ctf_SearchResults !global_request_id,
 Some (P_pl
  (CT_premises_list
  [CT_eval_result
    (xlate_formula ast,
    translate_constr env nvalue,
    translate_constr env ntyp)]))));;



(* The following function is copied from globpr in env/printer.ml *)
let globcv = function
  | Node(_,"MUTIND", (Path(_,sl,s))::(Num(_,tyi))::_) ->
       convert_qualid
	 (Global.qualid_of_global (IndRef(section_path sl s,tyi)))
  | Node(_,"MUTCONSTRUCT",(Path(_,sl,s))::(Num(_,tyi))::(Num(_,i))::_) ->
       convert_qualid
          (Global.qualid_of_global (ConstructRef ((section_path sl s, tyi), i)))
  | _ -> failwith "globcv : unexpected value";;

let pbp_tac_pcoq =
    pbp_tac (function x -> 
      output_results
  	[< 'fNL; 'sTR "message"; 'fNL; 'sTR "pbp_results"; 'fNL;
	  'iNT !global_request_id;  'fNL>]
       (Some (P_t(xlate_tactic x))));;


let dad_tac_pcoq =
  dad_tac(function x -> 
    output_results
    [< 'fNL; 'sTR "message"; 'fNL; 'sTR "pbp_results"; 'fNL;
       'iNT !global_request_id;  'fNL >]
    (Some (P_t(xlate_tactic x))));;

let search_output_results () =
  output_results
       (ctf_SearchResults !global_request_id)
       (Some (P_pl (CT_premises_list
                      (List.rev !ctv_SEARCH_LIST))));;


let debug_tac2_pcoq = function
    [Tacexp ast] ->
      (fun g ->
	let the_goal = ref (None : goal sigma option) in
	let the_ast = ref ast in
	let the_path = ref ([] : int list) in
	try
	  let result = report_error ast the_goal the_ast the_path [] g in
	  (errorlabstrm "DEBUG TACTIC"
	    [< 'sTR "no error here "; 'fNL; pr_goal (sig_it g);
	      'fNL; 'sTR "the tactic is"; 'fNL ; Printer.gentacpr ast >];
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
                                  (clean_path 0 ast 
					       (List.rev !the_path)))))));
	    	(output_results
		   (ctf_OtherGoal !global_request_id)
		   (Some (P_r (translate_goal (sig_it g)))));
	    raise e)
  | _ -> error "wrong arguments for debug_tac2_pcoq";;

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
			 let ((_, _, v), _, _) = get_variable sp in
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

let logical_kill n =
  let path = History.get_path_for_rank !current_proof_name n in
  begin
    traverse_to path;
    Pfedit.mutate weak_undo_pftreestate;
    (let kept_cmds, undone_cmds, remaining_goals, current_goal =
      History.logical_undo !current_proof_name n in
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

let command_changes = [
  ("TEXT_MODE",
   (function
     |  [VARG_AST (Id(_,x))] ->
	 (match x with
	   "on" -> (function () -> text_proof_flag := true)
	 | "off" -> (function () -> text_proof_flag := false)
	 | s -> errorlabstrm "TEXT_MODE" (make_error_stream 
					    ("Unexpected flag " ^ s)))
     | _ -> errorlabstrm "TEXT_MODE" 
           (make_error_stream "Unexpected argument")));

  ("StartProof", 
   (function
     | (VARG_STRING kind) ::
       ((VARG_IDENTIFIER s) ::
	((VARG_CONSTR c) :: [])) ->
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
		  [< 'sTR
                       "Let declarations can only be used in proof editing mode"
		  >];
		let str = (string_of_id s) in
		start_proof_com (Some s) stre c;
		History.start_proof str;
		current_proof_name := str;
		current_goal_index := 1
	    end
     | _ -> errorlabstrm "StartProof" (make_error_stream "StartProof")));
  
  ("GOAL", 
   (function
     | (VARG_CONSTR c) :: [] ->
	 (fun () ->
	    if not (refining ()) then
	      begin
		start_proof_com None NeverDischarge c;
		History.start_proof "Unnamed_thm";
		current_proof_name := "Unnamed_thm";
		current_goal_index := 1
	      end)
     | [] ->
	 (function () -> output_results_nl(ctf_EmptyGoalMessage ""))
     | _ -> errorlabstrm "Goal" (make_error_stream "Goal")));
  
  ("SOLVE",
   (function
     | [VARG_NUMBER n; VARG_TACTIC tcom] ->
       (fun () -> 
         if not (refining ()) then
           error "Unknown command of the non proof-editing mode";
         solve_nth n (Tacinterp.hide_interp tcom);
	 let old_n_count = History.border_length !current_proof_name in
	 let pf = proof_of_pftreestate (get_pftreestate ()) in
	 let n_goals = (List.length (fst (frontier pf))) + 1 - old_n_count in
	   begin
	     current_goal_index := n;
	     History.push_command !current_proof_name n n_goals
	   end)
     | _ -> errorlabstrm "SOLVE" (make_error_stream "SOLVE")));

  ("GOAL_CMD", 
   (function
     | (VARG_NUMBER n) ::
       ((VARG_TACTIC tac) :: []) ->
	 (function () -> 
	    let path = History.get_nth_open_path !current_proof_name n in
              solve_nth n (Tacinterp.hide_interp tac);
              traverse_to path;
              Pfedit.mutate weak_undo_pftreestate;
	      traverse_to [])
     | _ -> errorlabstrm "GOAL_CMD" (make_error_stream "GOAL_CMD")));
  
  ("KILL_NODE", 
   (function
     | (VARG_NUMBER n) :: [] ->
	 (function () -> 
	   let ngoals = kill_proof_node n in
	   output_results_nl
             (ctf_KilledMessage !global_request_id ngoals))
     | _ -> errorlabstrm "KILL_NODE" (make_error_stream "KILL_NODE")));
  ("KILL_SUB_PROOF",
   (function
     | [VARG_NUMBER n] ->
	 (function () -> logical_kill n)
     | _ -> errorlabstrm "KILL_SUB_PROOF" (make_error_stream "KILL_SUB_PROOF")));

  ("RESUME",
   (function [VARG_IDENTIFIER id] ->
     (fun () -> 
       let str = (string_of_id id) in
	 resume_proof id;
	 current_proof_name := str)
      | _ -> errorlabstrm "RESUME" (make_error_stream "RESUME")));

  ("BeginSilent", 
   (function
     | [] ->
	 (function
	     () ->
	       errorlabstrm "Begin Silent" 
		 [< 'sTR "not available in Centaur mode" >])
     | _ -> errorlabstrm "BeginSilent" (make_error_stream "BeginSilent")));
  
  ("EndSilent", 
   (function
     | [] ->
	 (function
	     () ->
	       errorlabstrm "End Silent"
		 [< 'sTR "not available in Centaur mode" >])
     | _ -> errorlabstrm "EndSilent" (make_error_stream "EndSilent")));
  
  ("SaveNamed", 
   (function
     | [] ->
	 (function () -> traverse_to []; save_named false)
     | _ -> errorlabstrm "SaveNamed" (make_error_stream "SaveNamed")));
  
  ("DefinedNamed", 
   (function
     | [] ->
	 (function () -> traverse_to []; save_named false)
     | _ -> errorlabstrm "DefinedNamed" (make_error_stream "DefinedNamed")));
  
  ("DefinedAnonymous", 
   (function
     | (VARG_IDENTIFIER id) :: [] ->
	 (function () ->
	   traverse_to [];
	   save_anonymous_thm true (string_of_id id))
     | _ ->
	 errorlabstrm "DefinedAnonymous"
	   (make_error_stream "DefinedAnonymous")));
  
    ("SaveAnonymous", 
   (function
     | (VARG_IDENTIFIER id) :: [] ->
	 (function () ->
	   traverse_to [];
	   save_anonymous_thm true (string_of_id id))
     | _ ->
	 errorlabstrm "SaveAnonymous"
	   (make_error_stream "SaveAnonymous")));
  
  ("SaveAnonymousThm", 
   (function
     | (VARG_IDENTIFIER id) :: [] ->
	 (function () ->
	   traverse_to [];
	   save_anonymous_thm true (string_of_id id))
     | _ ->
	 errorlabstrm "SaveAnonymousThm"
	   (make_error_stream "SaveAnonymousThm")));
  
  ("SaveAnonymousRmk", 
   (function
     | (VARG_IDENTIFIER id) :: [] ->
	 (function
	     () -> traverse_to [];
	       save_anonymous_remark true (string_of_id id))
     | _ ->
	 errorlabstrm "SaveAnonymousRmk"
	   (make_error_stream "SaveAnonymousRmk")));
  
  ("ABORT", 
   (function
     | (VARG_IDENTIFIER id) :: [] ->
	 (function
	     () ->
	       delete_proof id;
	       current_proof_name := "";
	       output_results_nl
		 (ctf_AbortedMessage !global_request_id (string_of_id id)))
     | [] ->
	 (function
	     () -> delete_current_proof ();
	     current_proof_name := "";
	       output_results_nl
		 (ctf_AbortedMessage !global_request_id ""))
     | _ -> errorlabstrm "ABORT" (make_error_stream "ABORT")));
  ("SEARCH",
   function
       (VARG_QUALID qid)::l ->
         (fun () -> 
           ctv_SEARCH_LIST:=[];
	    let global_ref = Vernacentries.global dummy_loc qid in
           filtered_search
             (filter_by_module_from_varg_list l)
	     add_search (Nametab.locate qid);
	   search_output_results())
     |	_ -> failwith "bad form of arguments");

  ("SearchRewrite",
   function
       (VARG_CONSTR c)::l ->
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
       (VARG_CONSTR c)::l ->
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
      | [VARG_QUALID qid] ->
	 (function () -> 
	   let results = xlate_vernac_list (name_to_ast qid) in
	   output_results 
	     [<'fNL; 'sTR "message"; 'fNL; 'sTR "PRINT_VALUE"; 'fNL >]
	     (Some (P_cl results)))
     | _ -> errorlabstrm "PrintId" (make_error_stream "PrintId")));
  
  ("Check", 
   (function
     | (VARG_STRING kind) :: ((VARG_CONSTR c) :: g) ->
	 let evmap, env =
	   Vernacentries.get_current_context_of_args g in
	 let f =
	   match kind with
	   | "CHECK" -> print_check
	   | "PRINTTYPE" ->
	       errorlabstrm "PrintType" [< 'sTR "Not yet supported in CtCoq" >]
	   | _ -> errorlabstrm "CHECK" (make_error_stream "CHECK") in
	 (function () -> 
	   let a,b = f (c, judgment_of_rawconstr evmap env c) in
	   output_results a b)
     | _ -> errorlabstrm "CHECK" (make_error_stream "CHECK")));
  
  ("Eval",
   (function
     | VARG_TACTIC_ARG(Redexp redexp):: VARG_CONSTR c :: g ->
	 let evmap, env = Vernacentries.get_current_context_of_args g in
	 let redfun =
	   ct_print_eval c (Tacred.reduction_of_redexp redexp env evmap) env in
	 fun () -> 
	   let strm, vtp = redfun evmap (judgment_of_rawconstr evmap env c) in
	   output_results strm vtp
     | _ -> errorlabstrm "Eval" (make_error_stream "Eval")));
  
  ("Centaur_Reset", 
   (function
     | (VARG_IDENTIFIER c) :: [] ->
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
	     [< 'fNL; 'sTR "message"; 'fNL; 'sTR "dad_rule_names"; 'fNL;
	       'iNT !global_request_id; 'fNL >]
	     (Some (P_ids
		      (CT_id_list
			 (List.map (fun s -> CT_ident s) results)))))
     | _ ->
	 errorlabstrm
	   "Show_dad_rules" (make_error_stream "Show_dad_rules")));
  ("INSPECT",
   (function
     | [VARG_NUMBER n] ->
         (function () -> inspect n)
     | _ -> errorlabstrm "INSPECT" (make_error_stream "INSPECT")))

];;

let non_debug_changes = [
  ("SHOW", 
   (function
     | [VARG_NUMBER n] -> (function () -> show_nth n)
     | _ -> errorlabstrm "SHOW" (make_error_stream "SHOW")))];;

let command_creations = [
  ("Comments",
   function l -> (fun () -> message ("Comments ok\n")));
  ("CommentsBold",
   function l -> (fun () -> message ("CommentsBold ok\n")));
  ("Title",
   function l -> (fun () -> message ("Title ok\n")));
  ("Author",
   function l -> (fun () -> message ("Author ok\n")));
  ("Note",
   function l -> (fun () -> message ("Note ok\n")));
  ("NL",
   function l -> (fun () -> message ("Newline ok\n")))];;



let start_pcoq_mode debug = 
  begin
    start_dad();
    set_xlate_mut_stuff globcv;
    declare_in_coq();
    add_tactic "PcoqPbp" pbp_tac_pcoq;
    add_tactic "Dad" dad_tac_pcoq;
    add_tactic "CtDebugTac" debug_tac2_pcoq;
    add_tactic "CtDebugTac2" debug_tac2_pcoq;
(* The following ones are added to enable rich comments in pcoq *)
    add_tactic "Image" (fun _ -> tclIDTAC);
    List.iter (fun (a,b) -> vinterp_add a b) command_creations;
    List.iter (fun (a,b) -> overwriting_vinterp_add a b) command_changes;
    if not debug then
      List.iter (fun (a,b) -> overwriting_vinterp_add a b) non_debug_changes;
  end;;

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

