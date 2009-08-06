(*i camlp4deps: "parsing/grammar.cma" i*)

(*
 * This file has been modified by Lionel Elie Mamane <lionel@mamane.lu>
 * to implement the following features
 * - Terms (optionally) as pretty-printed string and not trees
 * - (Optionally) give most commands their usual Coq semantics
 * - Add the backtracking information to the status message.
 * in the following time period
 * - May-November 2006
 * and
 * - Make use of new Command.save_hook to generate dependencies at
 *   save-time.
 * in
 *  - June 2007
 *)

(*Toplevel loop for the communication between Coq and Centaur *)
open Names;;
open Nameops;;
open Util;;
open Term;;
open Pp;;
open Ppconstr;;
open Prettyp;;
open Libnames;;
open Libobject;;
open Library;;
open Vernacinterp;;
open Evd;;
open Proof_trees;;
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
open Line_oriented_parser;;
open Xlate;;
open Vtp;;
open Ascent;;
open Translate;;
open Name_to_ast;;
open Pbp;;
open Blast;;
(* open Dad;; *)
open Debug_tac;;
open Search;;
open Constrintern;;
open Nametab;;
open Showproof;;
open Showproof_ct;;
open Tacexpr;;
open Vernacexpr;;
open Printer;;

let pcoq_started = ref None;;

let if_pcoq f a =
  if !pcoq_started <> None then f a else error "Pcoq is not started";;

let text_proof_flag = ref "en";;

let pcoq_history = ref true;;

let assert_pcoq_history f a =
  if !pcoq_history then f a else error "Pcoq-style history tracking deactivated";;

let current_proof_name () = 
  try 
    string_of_id (get_current_proof_name ())
  with
      UserError("Pfedit.get_proof", _) -> "";;

let current_goal_index = ref 0;;

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
  | P_ids x -> fID_LIST x)
  ++ (str "e\nblabla\n");;


(*Message functions, the text of these messages is recognized by the protocols *)
(*of CtCoq                                                                     *)
let ctf_header message_name request_id =
 str "message" ++ fnl() ++ str message_name ++ fnl() ++
 int request_id ++ fnl();;

let ctf_acknowledge_command request_id command_count opt_exn =
  let goal_count, goal_index = 
    if refining() then
      let g_count =
        List.length 
          (fst (frontier (proof_of_pftreestate (get_pftreestate ())))) in
        g_count, !current_goal_index
    else
      (0, 0)
  and statnum = Lib.current_state_label ()
  and dpth = let d = Pfedit.current_proof_depth() in if d >= 0 then d else 0
  and pending = CT_id_list (List.map xlate_ident (Pfedit.get_all_proof_names())) in
   (ctf_header "acknowledge" request_id ++
    int command_count ++ fnl() ++
    int goal_count ++ fnl () ++
    int goal_index ++ fnl () ++
    str (current_proof_name()) ++ fnl() ++
    int statnum ++ fnl() ++
    print_tree (P_ids pending) ++
    int dpth ++ fnl() ++
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

let ctf_GoalsReqIdMessage = ctf_header "goals_state";;

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


let break_happened = ref false;;

let output_results stream vtp_tree =
    let _ = Sys.signal Sys.sigint
       (Sys.Signal_handle(fun i -> (break_happened := true;()))) in
    msg (stream ++
    (match vtp_tree with
       Some t -> print_tree t
     | None -> mt()));;

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
    output_results (ctf_GoalReqIdMessage !global_request_id
		    ++ pr_nth_open_subgoal n)
      None
  with
  | Invalid_argument s -> 
       error "No focused proof (No proof-editing in progress)";;

let show_subgoals () =
  try
    output_results (ctf_GoalReqIdMessage !global_request_id
		    ++ pr_open_subgoals ())
      None
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
  let id_string =
    string_of_qualid (Nametab.shortest_qualid_of_global Idset.empty
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


let print_check env judg =
 ((ctf_SearchResults !global_request_id) ++
    print_judgment env judg,
  None);;

let ct_print_eval red_fun env evmap ast judg =
  (if refining() then traverse_to []);
  let {uj_val=value; uj_type=typ} = judg in
  let nvalue = (red_fun env evmap) value
    (* // Attention , ici il faut peut être utiliser des environnemenst locaux *)
  and ntyp = nf_betaiota typ in
    print_tree
      (P_pl
	 (CT_premises_list
	    [CT_eval_result
	       (xlate_formula ast,
		translate_constr false env nvalue,
		translate_constr false env ntyp)]));;

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

(* <\cpa> 
let dad_tac_pcoq =
  dad_tac(function x -> 
    output_results
    (ctf_header "pbp_results" !global_request_id)
    (Some (P_t(xlate_tactic x))));;
</cpa> *)

let search_output_results () =
  (* LEM: See comments for pcoq_search *)
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
	  let _result = report_error tac the_goal the_ast the_path [] g in
	  (errorlabstrm "DEBUG TACTIC"
	     (str "no error here " ++ fnl () ++ Printer.pr_goal (sig_it g) ++
	      fnl () ++ str "the tactic is" ++ fnl () ++
	      Pptactic.pr_glob_tactic (Global.env()) tac) (*
Caution, this is in the middle of what looks like dead code. ;
	   result *))
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
             	oname, Lib.Leaf lobj ->
		  (match oname, object_tag lobj with
                       (sp,_), "VARIABLE" ->
			 let (_, _, v) = Global.lookup_named (basename sp) in
			   add_search2 (Nametab.locate (qualid_of_path sp)) v
		     | (sp,kn), "CONSTANT" ->
			 let typ = Typeops.type_of_constant (Global.env()) (constant_of_kn kn) in
			   add_search2 (Nametab.locate (qualid_of_path sp)) typ
		     | (sp,kn), "MUTUALINDUCTIVE" ->
			 add_search2 (Nametab.locate (qualid_of_path sp))
			   (Pretyping.Default.understand Evd.empty (Global.env())
			      (RRef(dummy_loc, IndRef(kn,0))))
		     | _ -> failwith ("unexpected value 1 for "^ 
				      (string_of_id (basename (fst oname)))))
              | _ -> failwith "unexpected value")
	 with e -> ())
      l;
    output_results
      (ctf_SearchResults !global_request_id)
      (Some
         (P_pl (CT_premises_list (List.rev !ctv_SEARCH_LIST))));;

let ct_int_to_TARG n = 
	CT_coerce_FORMULA_OR_INT_to_TARG
	  (CT_coerce_ID_OR_INT_to_FORMULA_OR_INT
	     (CT_coerce_INT_to_ID_OR_INT (CT_int n)));;

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
  solve_nth n (Tacinterp.hide_interp tac (get_end_tac()));
  traverse_to path;
  Pfedit.mutate weak_undo_pftreestate;
  traverse_to []

let kill_node_verbose n =
  let ngoals = kill_proof_node n in
  output_results_nl (ctf_KilledMessage !global_request_id ngoals)

let set_text_mode s = text_proof_flag := s

let pcoq_reset_initial() =
  output_results(ctf_AbortedAllMessage()) None;
  Vernacentries.abort_refine Lib.reset_initial ();
  output_results(ctf_ResetInitialMessage()) None;;

let pcoq_reset x =
  if refining() then
    output_results (ctf_AbortedAllMessage ()) None;
    Vernacentries.abort_refine Lib.reset_name (dummy_loc,x);
    output_results
      (ctf_ResetIdentMessage !global_request_id (string_of_id x)) None;;


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
  [ "Goal" "Cmd" natural(n) "with" tactic(tac) ] -> [ assert_pcoq_history (simulate_solve n) tac ]
END

VERNAC COMMAND EXTEND KillProofAfter
| [ "Kill" "Proof" "after"  natural(n) ] -> [ assert_pcoq_history kill_node_verbose n ]
END

VERNAC COMMAND EXTEND KillProofAt
| [ "Kill" "Proof" "at"  natural(n) ] -> [ assert_pcoq_history kill_node_verbose n ]
END

VERNAC COMMAND EXTEND KillSubProof
  [ "Kill" "SubProof" natural(n) ] -> [ assert_pcoq_history logical_kill n ]
END

VERNAC COMMAND EXTEND PcoqReset
  [ "Pcoq" "Reset" ident(x) ] -> [ pcoq_reset x ]
END

VERNAC COMMAND EXTEND PcoqResetInitial
  [ "Pcoq" "ResetInitial" ] -> [ pcoq_reset_initial() ]
END

let start_proof_hook () =
  if !pcoq_history then History.start_proof (current_proof_name());
  current_goal_index := 1

let solve_hook n =
  current_goal_index := n;
  if !pcoq_history then
    let name = current_proof_name () in
    let old_n_count = History.border_length name in
    let pf = proof_of_pftreestate (get_pftreestate ()) in
    let n_goals = (List.length (fst (frontier pf))) + 1 - old_n_count in
      History.push_command name n n_goals

let abort_hook s = output_results_nl (ctf_AbortedMessage !global_request_id s)

let interp_search_about_item = function
  | SearchSubPattern pat ->
      let _,pat = Constrintern.intern_constr_pattern Evd.empty (Global.env()) pat in
      GlobSearchSubPattern pat
  | SearchString (s,_) ->
      warning "Notation case not taken into account";
      GlobSearchString s

let pcoq_search s l =
  (* LEM: I don't understand why this is done in this way (redoing the
   *      match on s here) instead of making the code in
   *      parsing/search.ml call the right function instead of
   *      "plain_display". Investigates this later.
   * TODO
   *)
  ctv_SEARCH_LIST:=[];
  begin match s with
  | SearchAbout sl -> 
      raw_search_about (filter_by_module_from_list l) add_search
	(List.map (on_snd interp_search_about_item) sl)
  | SearchPattern c ->
      let _,pat = intern_constr_pattern Evd.empty (Global.env()) c in
      raw_pattern_search (filter_by_module_from_list l) add_search pat
  | SearchRewrite c ->
      let _,pat = intern_constr_pattern Evd.empty (Global.env()) c in
      raw_search_rewrite (filter_by_module_from_list l) add_search pat;
  | SearchHead c ->
      let _,pat = intern_constr_pattern Evd.empty (Global.env()) c in
      raw_search_by_head (filter_by_module_from_list l) add_search pat;
  end;
  search_output_results()

(* Check sequentially whether the pattern is one of the premises *)
let rec hyp_pattern_filter pat name a c =
  let _c1 = strip_outer_cast c in
    match kind_of_term c with
      | Prod(_, hyp, c2) -> 
	  (try
(*	     let _ = msgnl ((str "WHOLE ") ++ (Printer.pr_lconstr c)) in
             let _ = msgnl ((str "PAT ") ++ (Printer.pr_constr_pattern pat)) in *)
             if Matching.is_matching pat hyp then
	       (msgnl (str "ok"); true)
	     else
	       false
           with UserError _ -> false) or
	  hyp_pattern_filter pat name a c2
      | _ -> false;;

let hyp_search_pattern c l =
  let _, pat = intern_constr_pattern Evd.empty (Global.env()) c in
    ctv_SEARCH_LIST := [];
    gen_filtered_search
      (fun s a c -> (filter_by_module_from_list l s a c &&
		     (if hyp_pattern_filter pat s a c then
		   	(msgnl (str "ok2"); true) else false)))
      (fun s a c -> (msgnl (str "ok3"); add_search s a c));
    output_results
      (ctf_SearchResults !global_request_id)
      (Some
	 (P_pl (CT_premises_list (List.rev !ctv_SEARCH_LIST))));;
let pcoq_print_name ref =
  output_results 
    (fnl () ++ str "message" ++ fnl () ++ str "PRINT_VALUE" ++ fnl () ++ print_name ref )
    None

let pcoq_print_check env j =
  let a,b = print_check env j in output_results a b

let pcoq_print_eval redfun env evmap c j =
  output_results
    (ctf_SearchResults !global_request_id
     ++ Prettyp.print_eval redfun env evmap c j)
    None;;

open Vernacentries

let pcoq_show_goal = function
  | Some n -> show_nth n
  | None -> show_subgoals ()
;;

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

let pcoq_term_pr = {
  pr_constr_expr   = (fun c -> str "pcoq_constr_expr\n"  ++ (default_term_pr.pr_constr_expr   c));
  (* In future translate_constr false (Global.env())
   * Except with right bool/env which I'll get :)
   *)
  pr_lconstr_expr  = (fun c -> fFORMULA (xlate_formula c) ++ str "(pcoq_lconstr_expr of " ++ (default_term_pr.pr_lconstr_expr  c) ++ str ")");
  pr_constr_pattern_expr  = (fun c -> str "pcoq_pattern_expr\n" ++ (default_term_pr.pr_constr_pattern_expr  c));
  pr_lconstr_pattern_expr = (fun c -> str "pcoq_constr_expr\n"  ++ (default_term_pr.pr_lconstr_pattern_expr c))
}

let start_pcoq_trees () =
  set_term_pr pcoq_term_pr

(* BEGIN functions for object_pr *)

(* These functions in general mirror what name_to_ast does in a subcase,
   and then print the corresponding object as a PCoq tree. *)

let object_to_ast_template object_to_ast_list sp =
  let l = object_to_ast_list sp in
    VernacList (List.map (fun x -> (dummy_loc, x)) l)

let pcoq_print_object_template object_to_ast_list sp =
  let results = xlate_vernac_list (object_to_ast_template object_to_ast_list sp) in
    print_tree (P_cl results)

(* This function mirror what print_check does *)

let pcoq_print_typed_value_in_env env (value, typ) =
 let value_ct_ast = 
     (try translate_constr false (Global.env()) value 
      with UserError(f,str) ->
           raise(UserError(f,Printer.pr_lconstr value ++
			      fnl () ++ str ))) in
 let type_ct_ast =
     (try translate_constr false (Global.env()) typ
      with UserError(f,str) ->
           raise(UserError(f, Printer.pr_lconstr value ++ fnl() ++ str))) in
   print_tree
     (P_pl
	(CT_premises_list
	   [CT_coerce_TYPED_FORMULA_to_PREMISE
	      (CT_typed_formula(value_ct_ast,type_ct_ast)
	      )]))
;;

(* This function mirrors what show_nth does *)

let pcoq_pr_subgoal n gl =
  try
    print_tree
      (if (!text_proof_flag<>"off") then
	   (* This is a horrendeous hack; it ignores the "gl" argument
              and just takes the currently focused proof. This will bite
	      us back one day.
	      TODO: Fix this.
	   *)
	   (
	    if not !pcoq_history then error "Text mode requires Pcoq history tracking.";
	    if n=0
	    then (P_text (show_proof !text_proof_flag []))
	    else
		let path = History.get_nth_open_path (current_proof_name()) n in
		  (P_text (show_proof !text_proof_flag path)))
       else
	   (let goal = List.nth gl (n - 1) in
	      (P_r (translate_goal goal))))
  with
  | Invalid_argument _
  | Failure "nth"
  | Not_found           -> error "No such goal";;

let pcoq_pr_subgoals close_cmd evar gl =
  (*LEM: TODO: we should check for evar emptiness or not, and do something *)
  try
    print_tree
      (if (!text_proof_flag<>"off") then
	   raise (Anomaly ("centaur.ml4:pcoq_pr_subgoals", str "Text mode show all subgoals not implemented"))
       else
	   (P_rl (translate_goals gl)))
  with
  | Invalid_argument _
  | Failure "nth"
  | Not_found           -> error "No such goal";;


(*  END functions for object_pr  *)

let pcoq_object_pr = {
  print_inductive           = pcoq_print_object_template inductive_to_ast_list;
  (* TODO: Check what that with_infos means, and adapt accordingly *)
  print_constant_with_infos = pcoq_print_object_template constant_to_ast_list;
  print_section_variable    = pcoq_print_object_template variable_to_ast_list;
  print_syntactic_def       = pcoq_print_object_template (fun x -> errorlabstrm "print"
      (str "printing of syntax definitions not implemented in PCoq syntax"));
  (* TODO: These are placeholders only; write them *)
  print_module              = (fun x y -> str "pcoq_print_module not implemented");
  print_modtype             = (fun x   -> str "pcoq_print_modtype not implemented");
  print_named_decl          = (fun x   -> str "pcoq_print_named_decl not implemented");
  (* TODO: Find out what the first argument x (a bool) is about and react accordingly *)
  print_leaf_entry          = (fun x -> pcoq_print_object_template leaf_entry_to_ast_list);
  print_library_entry       = (fun x y -> Some (str "pcoq_print_library_entry not implemented"));
  print_context             = (fun x y z -> str "pcoq_print_context not implemented");
  print_typed_value_in_env  = pcoq_print_typed_value_in_env;
  Prettyp.print_eval        = ct_print_eval;
};;

let pcoq_printer_pr = {
 pr_subgoals = pcoq_pr_subgoals;
 pr_subgoal  = pcoq_pr_subgoal;
 pr_goal     = (fun x   -> str "pcoq_pr_goal not implemented");
};;


let start_pcoq_objects () =
  set_object_pr pcoq_object_pr;
  set_printer_pr pcoq_printer_pr

let start_default_objects () =
  set_object_pr default_object_pr;
  set_printer_pr default_printer_pr

let full_name_of_ref r =
  (match r with
     | VarRef _ -> str "VAR"
     | ConstRef _ -> str "CST"
     | IndRef _ -> str "IND"
     | ConstructRef _ -> str "CSR")
  ++ str " " ++ (pr_path (Nametab.path_of_global r))
    (* LEM TODO: Cleanly separate path from id (see Libnames.string_of_path) *)

let string_of_ref =
  (*LEM TODO: Will I need the Var/Const/Ind/Construct info?*)
  Depends.o Libnames.string_of_path Nametab.path_of_global

let print_depends compute_depends ptree =
  output_results (List.fold_left (fun x y -> x ++ (full_name_of_ref y) ++ fnl())
		    (str "This object depends on:" ++ fnl())
		    (compute_depends ptree))
                 None

let output_depends compute_depends ptree =
  (* Using an ident list for that is arguably stretching it, but less effort than touching the vtp types *)
  output_results (ctf_header "depends" !global_request_id ++
		    print_tree (P_ids (CT_id_list (List.map
						     (fun x -> CT_ident (string_of_ref x))
						     (compute_depends ptree)))))
                 None

let gen_start_depends_dumps print_depends print_depends' print_depends'' print_depends''' =
  Command.set_declare_definition_hook (print_depends' (Depends.depends_of_definition_entry ~acc:[]));
  Command.set_declare_assumption_hook (print_depends  (fun (c:types) -> Depends.depends_of_constr c []));
  Command.set_start_hook (print_depends    (fun c -> Depends.depends_of_constr c []));
  Command.set_save_hook  (print_depends''  (Depends.depends_of_pftreestate Depends.depends_of_pftree));
  Refiner.set_solve_hook (print_depends''' (fun pt -> Depends.depends_of_pftree_head pt []))

let start_depends_dumps () = gen_start_depends_dumps output_depends output_depends output_depends output_depends

let start_depends_dumps_debug () = gen_start_depends_dumps print_depends print_depends print_depends print_depends

TACTIC EXTEND pbp
| [ "pbp" ident_opt(idopt) natural_list(nl) ] -> 
    [ if_pcoq pbp_tac_pcoq idopt nl ]
END

TACTIC EXTEND ct_debugtac
| [ "debugtac" tactic(t) ] -> [ if_pcoq debug_tac2_pcoq (fst t) ]
END

TACTIC EXTEND ct_debugtac2
| [ "debugtac2" tactic(t) ] -> [ if_pcoq debug_tac2_pcoq (fst t) ]
END


let start_pcoq_mode debug = 
  begin
    pcoq_started := Some debug;
(* <\cpa> 
    start_dad();
</cpa> *)
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
    start_pcoq_objects();
    Flags.print_emacs := false; Pp.make_pp_nonemacs(); 
  end;;


let start_pcoq () =
  start_pcoq_mode false;
  set_acknowledge_command ctf_acknowledge_command;
  set_start_marker "CENTAUR_RESERVED_TOKEN_start_command";
  set_end_marker "CENTAUR_RESERVED_TOKEN_end_command";
  raise Vernacexpr.ProtectedLoop;;

let start_pcoq_debug () =
  start_pcoq_mode true;
  set_acknowledge_command ctf_acknowledge_command;
  set_start_marker "--->";
  set_end_marker "<---";
  raise Vernacexpr.ProtectedLoop;;

VERNAC COMMAND EXTEND HypSearchPattern
  [ "HypSearchPattern" constr(pat) ] -> [ hyp_search_pattern pat ([], false) ]
END

VERNAC COMMAND EXTEND StartPcoq
  [ "Start" "Pcoq" "Mode" ] -> [ start_pcoq () ]
END

VERNAC COMMAND EXTEND Pcoq_inspect
  [ "Pcoq_inspect" ] -> [ inspect 15 ]
END

VERNAC COMMAND EXTEND StartPcoqDebug
| [ "Start" "Pcoq" "Debug" "Mode" ] -> [ start_pcoq_debug () ]
END

VERNAC COMMAND EXTEND StartPcoqTerms
| [ "Start" "Pcoq" "Trees" ] -> [ start_pcoq_trees () ]
END

VERNAC COMMAND EXTEND StartPcoqObjects
| [ "Start" "Pcoq" "Objects" ] -> [ start_pcoq_objects () ]
END

VERNAC COMMAND EXTEND StartDefaultObjects
| [ "Start" "Default" "Objects" ] -> [ start_default_objects () ]
END

VERNAC COMMAND EXTEND StartDependencyDumps
| [ "Start" "Dependency" "Dumps" ] -> [ start_depends_dumps () ]
END

VERNAC COMMAND EXTEND StopPcoqHistory
| [ "Stop" "Pcoq" "History" ] -> [ pcoq_history := false ]
END
