(*i camlp4deps: "parsing/grammar.cma" i*)

(*Toplevel loop for the communication between Coq and Centaur *)
open Names;;
open Nameops;;
open Util;;
open Term;;
open Pp;;
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

let pcoq_started = ref None;;

let if_pcoq f a =
  if !pcoq_started <> None then f a else error "Pcoq is not started";;

let text_proof_flag = ref "en";;

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


let print_check judg =
 let {uj_val=value; uj_type=typ} = judg in
 let value_ct_ast = 
     (try translate_constr false (Global.env()) value 
      with UserError(f,str) ->
           raise(UserError(f,Printer.pr_lconstr value ++
			      fnl () ++ str ))) in
 let type_ct_ast =
     (try translate_constr false (Global.env()) typ
      with UserError(f,str) ->
           raise(UserError(f, Printer.pr_lconstr value ++ fnl() ++ str))) in
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
			 let (_, _, v) = get_variable (basename sp) in
			   add_search2 (Nametab.locate (qualid_of_sp sp)) v
		     | (sp,kn), "CONSTANT" ->
			 let {const_type=typ} = Global.lookup_constant (constant_of_kn kn) in
			   add_search2 (Nametab.locate (qualid_of_sp sp)) typ
		     | (sp,kn), "MUTUALINDUCTIVE" ->
			 add_search2 (Nametab.locate (qualid_of_sp sp))
			   (Pretyping.understand Evd.empty (Global.env())
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

VERNAC COMMAND EXTEND PcoqReset
  [ "Pcoq" "Reset" ident(x) ] -> [ pcoq_reset x ]
END

VERNAC COMMAND EXTEND PcoqResetInitial
  [ "Pcoq" "ResetInitial" ] -> [ pcoq_reset_initial() ]
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

let interp_search_about_item = function
  | SearchRef qid -> GlobSearchRef (Nametab.global qid)
  | SearchString s -> GlobSearchString s

let pcoq_search s l =
  ctv_SEARCH_LIST:=[];
  begin match s with
  | SearchAbout sl -> 
      raw_search_about (filter_by_module_from_list l) add_search
	(List.map interp_search_about_item sl)
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

(* Check sequentially whether the pattern is one of the premises *)
let rec hyp_pattern_filter pat name a c =
  let _c1 = strip_outer_cast c in
    match kind_of_term c with
      | Prod(_, hyp, c2) -> 
	  (try
(*	     let _ = msgnl ((str "WHOLE ") ++ (Printer.pr_lconstr c)) in
             let _ = msgnl ((str "PAT ") ++ (Printer.pr_pattern pat)) in *)
             if Matching.is_matching pat hyp then
	       (msgnl (str "ok"); true)
	     else
	       false
           with UserError _ -> false) or
	  hyp_pattern_filter pat name a c2
      | _ -> false;;

let hyp_search_pattern c l =
  let _, pat = interp_constrpattern Evd.empty (Global.env()) c in
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
  let results = xlate_vernac_list (name_to_ast ref) in
  output_results 
    (fnl () ++ str "message" ++ fnl () ++ str "PRINT_VALUE" ++ fnl ())
    (Some (P_cl results))

let pcoq_print_check j =
  let a,b = print_check j in output_results a b

let pcoq_print_eval redfun env c j =
  let strm, vtp = ct_print_eval c redfun env j in
  output_results strm vtp;;

open Vernacentries

let pcoq_show_goal = function
  | Some n -> show_nth n
  | None ->
      if !pcoq_started = Some true (* = debug *) then
	msg (Printer.pr_open_subgoals ())
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
    declare_in_coq();
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
