
(* $Id$ *)

(* Concrete syntax of the mathematical vernacular MV V2.6 *)

open Pp
open System
open Names
open Term
open Reduction
open Tacmach
open Pfedit
open Proof_trees
open Library
open Libobject
open Environ
open States
open Vernacinterp
open Declare
open Coqast
open Ast
open Evd


(* Dans join_binders, s'il y a un "?", on perd l'info qu'il est partagé *)
let join_binders binders = 
  List.flatten
    (List.map (fun (idl,c) -> List.map (fun id -> (id,c)) idl) binders)

let add = vinterp_add

(* equivalent to pr_subgoals but start from the prooftree and 
   check for uninstantiated existential variables *)

let pr_subgoals_of_pfts pfts = 
  let gls = fst (frontier (proof_of_pftreestate pfts)) in 
  let sigma = project (top_goal_of_pftreestate pfts) in
  pr_subgoals_existential sigma gls

let show_script () =
  let pts = get_pftreestate () in
  let pf = proof_of_pftreestate pts
  and evc = evc_of_pftreestate pts in
  mSGNL(Refiner.print_script true (ts_it evc) (initial_sign()) pf)

let show_prooftree () =
  let pts = get_pftreestate () in
  let pf = proof_of_pftreestate pts
  and evc = evc_of_pftreestate pts in
  mSG(Refiner.print_proof (ts_it evc) (initial_sign()) pf)

let show_open_subgoals () =
  let pfts = get_pftreestate () in
  mSG(pr_subgoals_of_pfts pfts)

let show_nth_open_subgoal n =
  let pf = proof_of_pftreestate (get_pftreestate ()) in
  mSG(pr_subgoal n (fst(frontier pf)))

let show_open_subgoals_focused () =
  let pfts = get_pftreestate () in
  match focus() with
    | 0 -> 
	mSG(pr_subgoals_of_pfts pfts)
    | n -> 
	let pf = proof_of_pftreestate pfts in
	let gls = fst(frontier pf) in 
	if n > List.length gls then 
	  (make_focus 0; mSG(pr_subgoals_of_pfts pfts))
	else if List.length gls < 2 then 
	  mSG(pr_subgoal n gls)
	else 
	  mSG (v 0 [< 'iNT(List.length gls); 'sTR" subgoals"; 'cUT; 
		      pr_subgoal n gls >])

let show_node () =
  let pts = get_pftreestate () in
  let pf = proof_of_pftreestate pts
  and evc = evc_of_pftreestate pts
  and cursor = cursor_of_pftreestate pts in
  mSG [< prlist_with_sep pr_spc pr_int (List.rev cursor); 'fNL ;
         prgl pf.goal ; 'fNL ;
         (match pf.ref with
            | None -> [< 'sTR"BY <rule>" >]
            | Some(r,spfl) ->
		[< 'sTR"BY "; Refiner.pr_rule r; 'fNL; 'sTR"  ";
		   hOV 0 (prlist_with_sep pr_fnl prgl
			    (List.map (fun p -> p.goal) spfl)) >]);
         'fNL >]
    
let show_top_evars () =
  let pfts = get_pftreestate () in 
  let gls = top_goal_of_pftreestate pfts in 
  let sigma = project gls in 
  mSG (pr_evars_int 1 (Evd.non_instantiated sigma))

(* Focus commands *)
let reset_top_of_tree () = 
  let pts = get_pftreestate () in 
  if not (is_top_pftreestate pts) then mutate top_of_tree

(* Locate commands *)
 
let locate_file f =
  try
    mSG [< 'sTR (System.where_in_path (System.search_paths()) f) ; 'fNL >]
  with Not_found -> 
    mSG [< 'sTR"Can't find file" ; 'sPC ; 'sTR f ; 'sPC ;
           'sTR"on loadpath" ; 'fNL >]

let locate_id id =
  try
    mSG [< 'sTR (string_of_path (Nametab.sp_of_id CCI id)) ; 'fNL >]
  with Not_found -> 
    error ((string_of_id id) ^ " not a defined object")

let print_loadpath () =
  let l = search_paths () in
  mSGNL [< 'sTR"Load Path:" ; 'fNL; 'sTR"  ";
           hV 0 (prlist_with_sep pr_fnl (fun s -> [< 'sTR s >]) l) >]

let goal_of_args = function
  | [VARG_NUMBER n] -> Some n
  | [] -> None
  | _ -> bad_vernac_args "goal_of_args"

let isfinite = function 
  | "Inductive"   -> true 
  | "CoInductive" -> false
  | _ -> anomaly "Unexpected string"

(* Locate commands *)
let _ = 
  add "LocateFile"
    (function 
       | [VARG_STRING f] -> (fun () -> locate_file f)
       | _ -> bad_vernac_args "LocateFile")

let _ = 
  add "LocateLibrary"
    (function 
       | [VARG_IDENTIFIER id] ->
	   (fun () -> locate_file ((string_of_id id)^".vo"))
       | _ -> bad_vernac_args "LocateLibrary")

let _ = 
  add "Locate"
    (function 
       | [VARG_IDENTIFIER id] -> (fun () -> locate_id id)
       | _  -> bad_vernac_args "Locate")

let _ = 
  add "ADDPATH"
    (function 
       | [VARG_STRING dir] -> (fun () -> add_path dir)
       | _ -> bad_vernac_args "ADDPATH")

let _ =
  add "DELPATH"
    (function 
       | [VARG_STRING dir] -> (fun () -> del_path dir)
       | _ -> bad_vernac_args "DELPATH")

let _ = 
  add "RECADDPATH"
    (function 
       | [VARG_STRING dir] -> (fun () -> radd_path dir)
       | _ -> bad_vernac_args "RECADDPATH")

let _ = 
  add "PrintPath"
    (function 
       | [] -> (fun () -> print_loadpath ())
       | _  -> bad_vernac_args "PrintPath")

let _ =
  add "PWD"
    (function 
       | [] -> (fun () -> print_endline (System.getcwd()))
       | _  -> bad_vernac_args "PWD")

let _ =
  add "DROP"
    (function 
       | [] -> (fun () -> raise Drop)
       | _  -> bad_vernac_args "DROP")

let _ =
  add "PROTECTEDLOOP"
    (function 
       | [] -> (fun () -> raise ProtectedLoop)
       | _  -> bad_vernac_args "PROTECTEDLOOP")

let _ =
  add "QUIT"
    (function 
       | [] -> (fun () -> raise Quit)
       | _  -> anomaly "To fill the empty holes...")

let _ =
  add "CD"
    (function  
       | [VARG_STRING s] ->
	   (fun () ->
              begin
		try Sys.chdir (glob s)
		with Sys_error str -> warning ("Cd failed: " ^ str)
	      end;
              print_endline (System.getcwd()))
       | [] -> (fun () -> print_endline (System.getcwd()))
       | _  -> bad_vernac_args "CD")

(* Managing states *)

let _ =
  add "SaveState"
    (function 
       | [VARG_IDENTIFIER name; VARG_STRING desc] ->
	   (fun () -> save_state (string_of_id name) desc)
       | _ -> bad_vernac_args "SaveState")

let _ =
  add "RestoreState"
    (function 
       | [VARG_IDENTIFIER name] ->
	   (fun () -> restore_state (string_of_id name))
       | _ -> bad_vernac_args "RestoreState")

let _ =
  add "RemoveState"
    (function 
       |[VARG_IDENTIFIER id] ->
	   (fun () ->
              let str = (string_of_id id) in
              if str = "Initial" then error "Cannot forget Initial";
              forget_state (is_silent()) str)
       | _ -> bad_vernac_args "RemoveState")

let _ =
  add "WriteStates"
    (function 
       | [arg] ->
	   (fun () -> 
              let s = (match arg with
			 | VARG_IDENTIFIER id -> string_of_id id
			 | VARG_STRING s -> s
			 | _ -> anomaly "To fill the empty holes...")
              in 
	      extern_state s)
       | _ -> bad_vernac_args "WriteStates")

let _ =
  add "PrintStates"
    (function 
       | [] -> 
	   (fun () ->
              mSG (prlist (fun (n,desc) -> 
			     [< 'sTR n; 'sTR" : "; 'sTR desc ; 'fNL >])
                     (list_saved_states())))
       | _ -> bad_vernac_args "PrintStates")

(* Resetting *)

let _ =
  add "ResetAfter"
    (function 
       | [VARG_IDENTIFIER id] -> (fun () -> reset_keeping_name id)
       | _ -> bad_vernac_args "ResetAfter")

let _ =
  add "ResetInitial"
    (function 
       | [] -> (fun () -> reset_initial ())
       | _  -> bad_vernac_args "ResetInitial")

let _ =
  add "ResetSection"
    (function 
       | [VARG_IDENTIFIER id] ->
	   (fun () -> reset_section (string_of_id id))
       | _ -> bad_vernac_args "ResetSection")

let _ =
  add "ResetName"
    (function 
       | [VARG_IDENTIFIER id] -> (fun () -> reset_name id)
       | _ -> bad_vernac_args "ResetName")

(* Modules *)

let _ =
  add "BeginModule"
    (function 
       | [VARG_IDENTIFIER id] ->
	   fun () -> Library.open_module (string_of_id id)
       | _ -> bad_vernac_args "BeginModule")

let _ =
  add "ReadModule"
    (function 
       | [VARG_IDENTIFIER id] ->
	   fun () -> 
	     without_mes_ambig Library.read_module (string_of_id id) None
       | _ -> bad_vernac_args "ReadModule")

let _ =
  add "PrintModules"
    (function 
       | [] -> 
	   (fun () ->
              let opened = Library.search_imports ()
	      and loaded = Library.search_modules () in
              mSG [< 'sTR"Imported (open) Modules: " ;
		     hOV 0 (prlist_with_sep pr_fnl
			      (fun sp -> [< 'sTR(string_of_path sp) >]) 
			      opened) ; 
		     'fNL ;
		     'sTR"Loaded Modules: " ;
		     hOV 0 (prlist_with_sep pr_fnl
			      (fun (s,sp) -> [< 'sTR s ; 'sTR" = " ;
						'sTR(string_of_path sp) >]) 
			      loaded) ;
		     'fNL >])
       | _ -> bad_vernac_args "PrintModules")

(* Sections *)

let _ =
  add "BeginSection"
    (function 
       | [VARG_IDENTIFIER id] ->
	   (fun () -> open_section (string_of_id id))
       | _ -> bad_vernac_args "BeginSection")

let _ =
  add "EndSection"
    (function 
       | [VARG_IDENTIFIER id] ->
	   (fun () ->
              if refining () then 
		errorlabstrm "vernacentries : EndSection"
		  [< 'sTR"proof editing in progress" ; (msg_proofs false) ;
                     'sTR"Use \"Abort All\" first or complete proof(s)." >];
              close_section_or_module (not (is_silent())) (string_of_id id))
       | _ -> bad_vernac_args "EndSection")

(* Proof switching *)

let _ =
  add "GOAL"
    (function 
       | [VARG_COMMAND com] ->
	   (fun () ->
              if not (refining()) then begin
              	start_proof "Unnamed_thm" NeverDischarge com;
		if not (is_silent()) then show_open_subgoals ()
              end else 
		error "repeated Goal not permitted in refining mode")
       | [] -> (fun () -> ())
       | _  -> bad_vernac_args "GOAL")

let _ =
  add "ABORT"
    (function 
       | [VARG_IDENTIFIER id] -> 
	   (fun () -> 
	      let s = string_of_id id in
	      abort_goal s; message ("Goal "^s^" aborted"))
       | [] -> (fun () -> abort_cur_goal (); message "Current goal aborted")
       | _  -> bad_vernac_args "ABORT")

let _ =
  add "ABORTALL"
    (function 
       | [] -> (fun () -> abort_goals())
       | _  -> bad_vernac_args "ABORTALL")

let _ =
  add "RESTART"
    (function 
       | [] -> (fun () -> (restart();show_open_subgoals ()))
       | _  -> bad_vernac_args "RESTART")

let _ =
  add "SUSPEND"
    (function 
       | [] -> (fun () -> set_proof None)
       | _  -> bad_vernac_args "SUSPEND")

let _ =
  add "RESUME"
    (function 
       | [VARG_IDENTIFIER id] ->
	   (fun () -> set_proof (Some(string_of_id id)))
       | [] -> (fun () -> resume_last ())
       | _  -> bad_vernac_args "RESUME")

let _ =
  add "FOCUS"
    (function 
       | [] -> 
	   (fun () -> make_focus 1; show_open_subgoals_focused ())
       | [VARG_NUMBER n] -> 
	   (fun () -> traverse_nth_goal n; show_open_subgoals_focused ())
       | _  -> bad_vernac_args "FOCUS")

(* Reset the focus to the top of the tree *)

let _ =
  add "UNFOCUS"
    (function 
       | [] -> 
	   (fun () -> 
	      make_focus 0; reset_top_of_tree (); show_open_subgoals ())
       | _  -> bad_vernac_args "UNFOCUS")

let _ =          
  add "IMPLICIT_ARGS_ON"
    (function 
       | [] -> (fun () -> make_implicit_args true)
       | _  -> bad_vernac_args "IMPLICIT_ARGS_ON")

let _ =
  add "IMPLICIT_ARGS_OFF"
    (function 
       | [] -> (fun () -> make_implicit_args false)
       | _  -> bad_vernac_args "IMPLICIT_ARGS_OFF")

let _ =
  add "SaveNamed"
    (function 
       | [] -> 
	   (fun () -> if not(is_silent()) then show_script(); save_named true)
       | _ -> bad_vernac_args "SaveNamed")

let _ =
  add "DefinedNamed"
    (function 
       | [] -> 
	   (fun () -> if not(is_silent()) then show_script(); save_named false)
       | _ -> bad_vernac_args "DefinedNamed")

let _ =
  add "SaveAnonymousThm"
    (function 
       | [VARG_IDENTIFIER id] -> 
	   (fun () -> 
	      if not(is_silent()) then show_script();
              save_anonymous_thm true (string_of_id id))
       | _ -> bad_vernac_args "SaveAnonymousThm")

let _ =
  add "SaveAnonymousRmk"
    (function 
       | [VARG_IDENTIFIER id] -> 
	   (fun () -> 
	      if not(is_silent()) then show_script();
              save_anonymous_remark true (string_of_id id))
       | _ -> bad_vernac_args "SaveAnonymousRmk")

let _ =
  add "TRANSPARENT"
    (fun id_list () ->
       List.iter 
	 (function 
	    | VARG_IDENTIFIER id -> set_transparent id
	    |   _  -> bad_vernac_args "TRANSPARENT")
	 id_list)
    
let _ =
  add "OPAQUE"
    (fun id_list () ->
       List.iter
	 (function 
	    | VARG_IDENTIFIER id -> set_opaque id
	    |   _  -> bad_vernac_args "OPAQUE")
	 id_list)

let _ =
  add "UNDO"
    (function 
       | [VARG_NUMBER n] ->
	   (fun () -> (undo n;show_open_subgoals_focused()))
       | _ -> bad_vernac_args "UNDO")

let _ =
  add "SHOW"
    (function 
       | [] -> (fun () -> show_open_subgoals ())
       | [VARG_NUMBER n] -> (fun () -> show_nth_open_subgoal n)
       | _ -> bad_vernac_args "SHOW")

let _ =
  add "SHOWIMPL"
    (function
       | [] -> (fun () -> with_implicits show_open_subgoals ())
       | [VARG_NUMBER n] -> (fun () -> with_implicits show_nth_open_subgoal n)
       | _ -> bad_vernac_args "SHOWIMPL")

let _ =
  add "ShowNode"
    (function 
       | [] -> (fun () -> show_node())
       | _  -> bad_vernac_args "ShowNode")

let _ =
  add "ShowEx"
    (function 
       | [] -> (fun () -> show_top_evars ())
       | _  -> bad_vernac_args "ShowEx")

let _ =
  add "Go"
    (function 
       | [VARG_NUMBER n] ->
	   (fun () -> (traverse n;show_node()))
       | [VARG_STRING"top"] ->
           (fun () -> (mutate top_of_tree;show_node()))
       | [VARG_STRING"next"] ->
           (fun () -> (mutate next_unproven;show_node()))
       | [VARG_STRING"prev"] ->
           (fun () -> (mutate prev_unproven;show_node()))
       | _ -> bad_vernac_args "Go")

let _ =
  add "ShowProof"
    (function 
       | [] ->
	   (fun () ->
	      let pts = get_pftreestate () in
	      let pf = proof_of_pftreestate pts in
	      let cursor = cursor_of_pftreestate pts in
	      let evc = ts_it (evc_of_pftreestate pts) in
	      let (pfterm,meta_types) = 
		Refiner.extract_open_proof pf.goal.hyps pf in
	      mSGNL [< 'sTR"LOC: " ;
		       prlist_with_sep pr_spc pr_int (List.rev cursor); 'fNL ;
		       'sTR"Subgoals" ; 'fNL ;
		       prlist
			 (fun (mv,ty) -> 
			    [< 'iNT mv ; 'sTR" -> " ; prterm ty ; 'fNL >])
			 meta_types;
		       'sTR"Proof: " ; prterm (nf_ise1 evc pfterm) >])
       | _ -> bad_vernac_args "ShowProof")

let _ =
  add "CheckGuard"
    (function 
       | [] ->
	   (fun () ->
	      let pts = get_pftreestate () in
	      let pf = proof_of_pftreestate pts 
	      and cursor = cursor_of_pftreestate pts in
	      let (pfterm,meta_types) = 
		Refiner.extract_open_proof pf.goal.hyps pf in
	      let message = 
		try 
		  Typing.control_only_guard empty_evd pfterm; 
		  [< 'sTR "The condition holds up to here" >]
                with UserError(_,s) -> 
		  [< 'sTR ("Condition violated : ") ;s >]
	      in 
	      mSGNL message)
       | _ -> bad_vernac_args "CheckGuard")

let _ =
  add "ShowTree"
    (function 
       | [] -> (fun () -> show_prooftree())
       | _  -> bad_vernac_args "ShowTree")

let _ =
  add "ShowScript"
    (function 
       | [] -> (fun () -> show_script())
       | _  -> bad_vernac_args "ShowScript")

let _ =
  add "ExplainProof"
    (function l ->
       let l = List.map (function 
			   | (VARG_NUMBER n) -> n 
                           |   _   -> bad_vernac_args "ExplainProof") l
       in
       fun () ->
         let pts = get_pftreestate() in
         let evc = evc_of_pftreestate pts in
         let rec aux pts = function
           | [] -> pts
           | (n::l) -> aux (Tacmach.traverse n pts) l in 
         let pts = aux pts (l@[-1]) in
         let pf = proof_of_pftreestate pts in 
	 mSG (Refiner.print_script true (ts_it evc) (initial_sign()) pf))

let _ =
  add "ExplainProofTree"
    (function l ->
       let l = List.map (function 
			   | (VARG_NUMBER n) -> n
			   |   _  -> bad_vernac_args "ExplainProofTree") l
       in 
       fun () ->
         let pts = get_pftreestate() in
         let evc = evc_of_pftreestate pts in
         let rec aux pts = function
           | [] -> pts
           | (n::l) -> aux (Tacmach.traverse n pts) l in 
         let pts = aux pts (l@[-1]) in
         let pf = proof_of_pftreestate pts in 
	 mSG (Refiner.print_proof (ts_it evc) (initial_sign()) pf))

let _ =
  add "ShowProofs"
    (function [] ->
       (fun () ->
	  let l = Pfedit.list_proofs() in 
	  mSGNL (prlist_with_sep pr_spc pr_str l))
       | _  -> bad_vernac_args "ShowProofs")

let _ =
  add "PrintAll"
    (function 
       | [] -> (fun () -> mSG(print_full_context_typ ()))
       | _  -> bad_vernac_args "PrintAll")

let _ =
  add "PRINT"
    (function 
       | [] -> (fun () -> mSG(print_local_context()))
       | _  -> bad_vernac_args "PRINT")

(* Pris en compte dans PrintOption *)

let _ =
  add "PrintId"
    (function 
       | [VARG_IDENTIFIER id] -> (fun () -> mSG(Pretty.print_name id))
       | _ -> bad_vernac_args "PrintId")

let _ =
  add "PrintOpaqueId"
    (function 
       | [VARG_IDENTIFIER id] -> (fun () -> mSG(print_opaque_name id))
       | _ -> bad_vernac_args "PrintOpaqueId")

let _ =
  add "PrintSec"
    (function 
       | [VARG_IDENTIFIER id] -> 
	   (fun () -> mSG(print_sec_context_typ (string_of_id id)))
       | _ -> bad_vernac_args "PrintSec")

let _ =
  add "BeginSilent"
    (function 
       | [] -> (fun () -> make_silent true)
       | _  -> bad_vernac_args "BeginSilent")

let _ =
  add "EndSilent"
    (function 
       | [] -> (fun () -> make_silent false)
       | _  -> bad_vernac_args "EndSilent")

let _ =
  add "StartProof"
    (function 
       | [VARG_STRING kind;VARG_IDENTIFIER s;VARG_COMMAND c] ->
	   let stre = match kind with
	     | "THEOREM" -> NeverDischarge
             | "LEMMA" -> NeverDischarge
             | "FACT" -> make_strength(safe_cdr (Library.cwd()))
             | "REMARK" -> make_strength(Library.cwd())
             | "DEFINITION" -> NeverDischarge
              | "LET" -> make_strength(safe_cddr (Library.cwd()))
              | "LOCAL" -> make_strength(Library.cwd())
              | _       -> anomaly "Unexpected string"
           in 
	   fun () ->
             begin
               start_proof (string_of_id s) stre c;
               if (not(is_silent())) then show_open_subgoals()
             end
       | _ -> bad_vernac_args "StartProof")

let _ =
  add "TheoremProof"
    (function 
       | [VARG_STRING kind; VARG_IDENTIFIER s; 
	  VARG_COMMAND c; VARG_VARGLIST coml] ->
	   let calls = List.map
			 (function 
			    | (VCALL(na,l)) -> (na,l)
			    | _ -> bad_vernac_args "")
			 coml 
	   in
	   let (stre,opacity) = match kind with
	     | "THEOREM" -> (NeverDischarge,true)
             | "LEMMA" -> (NeverDischarge,true)
             | "FACT" -> (make_strength(safe_cdr (Library.cwd())),true)
             | "REMARK" -> (make_strength(Library.cwd()),true)
             | "DEFINITION" -> (NeverDischarge,false)
             | "LET" -> (make_strength(safe_cdr (Library.cwd())),false)
             | "LOCAL" -> (make_strength(Library.cwd()),false)
             | _       -> anomaly "Unexpected string" 
	   in
           (fun () ->
              try
            	Library.with_heavy_rollback
		  (fun () ->
                     start_proof (string_of_id s) stre c;
                     if not (is_silent()) then show_open_subgoals();
                     List.iter Vernacinterp.call calls;
                     if not (is_silent()) then show_script();
                     save_named opacity)
		  ()
              with e ->
            	if is_unsafe "proof" then begin
                  mSGNL [< 'sTR"Error: checking of theorem " ; print_id s ;
                           'sPC ; 'sTR"failed" ;
                           'sTR"... converting to Axiom" >];
                  del_proof (string_of_id s);
                  parameter_def_var (string_of_id s) c
           	end else 
		  errorlabstrm "vernacentries__TheoremProof"
                    [< 'sTR"checking of theorem " ; print_id s ; 'sPC ;
                       'sTR"failed... aborting" >])
       | _ -> bad_vernac_args "TheoremProof")

let _ =
  add "DEFINITION"
    (function 
       | (VARG_STRING kind :: VARG_IDENTIFIER id :: VARG_COMMAND c ::optred) ->
	   let red_option = match optred with 
	     | [] -> None
	     | [VARG_TACTIC_ARG (REDEXP(r1,r2))] -> 
		 let (evmap,sign) = initial_sigma_sign() in
		 let redexp = redexp_of_ast evmap sign (r1,r2) in 
		 Some redexp
	     | _ -> bad_vernac_args "DEFINITION"
	   in 
	   let stre,coe,objdef,idcoe = match kind with
	     | "DEFINITION" -> NeverDischarge,false,false,false
             | "COERCION" -> NeverDischarge,true,false,false
             | "LCOERCION" -> make_strength(Library.cwd()),true,false,false
             | "LET" -> 
		 make_strength(safe_cddr (Library.cwd())),false,false,false
             | "LOCAL" -> make_strength(Library.cwd()),false,false,false
             | "OBJECT" -> NeverDischarge,false,true,false
             | "LOBJECT" -> make_strength(Library.cwd()),false,true,false
             | "OBJCOERCION" -> NeverDischarge,true,true,false
             | "LOBJCOERCION" -> make_strength(Library.cwd()),true,true,false
             | "SUBCLASS" -> NeverDischarge,false,false,true
             | "LSUBCLASS" -> make_strength(Library.cwd()),false,false,true
             | _       -> anomaly "Unexpected string"
	   in 
	   fun () ->
	     definition_body_red id stre c red_option;
	     message ((string_of_id id) ^ " is defined");
             if coe then begin
	       Class.try_add_new_coercion (Some id) stre None None false;
               message ((string_of_id id) ^ " is now a coercion")
	     end;
	     if idcoe then 
	       Class.try_add_new_coercion None stre (Some (Left id)) None true;
             if objdef then Recordobj.objdef_declare id
       | _ -> bad_vernac_args "DEFINITION")

let _ =
  add "VARIABLE"
    (function 
       | [VARG_STRING kind; VARG_BINDERLIST slcl] ->
	   if List.length slcl = 1 & List.length (fst (List.hd slcl)) = 1 then
             (match kind with
		| "VARIABLES" -> warning "Many variables are expected"
		| "HYPOTHESES" -> warning "Many hypotheses are expected"
		| "COERCIONS" -> warning "Many hypotheses are expected"
		| _ -> ());
	   let coe = match kind with   
	     | "COERCION" -> true
             | "COERCIONS" -> true
             | _ -> false
	   in
	   let stre = make_strength(Library.cwd ()) in
	   fun () ->
	     List.iter 
	       (fun (sl,c) -> 
		  List.iter 
		    (fun s ->
                       hypothesis_def_var (refining()) (string_of_id s) 
			 stre c;
                       if coe then
			 Class.try_add_new_coercion (Some s) 
			   stre None None false;
		       message ((string_of_id s) ^ " is assumed"))
                    sl)
	       slcl
       | _ -> bad_vernac_args "VARIABLE")
    
let _ =
  add "PARAMETER"
    (function 
       | [VARG_STRING kind; VARG_BINDERLIST slcl] ->
	   if List.length slcl = 1 & List.length (fst (List.hd slcl)) = 1 &
	      kind = "PARAMETERS" then warning "Many parameters are expected";
	   fun () ->
	     List.iter 
	       (fun (sl,c) ->
		  List.iter 
		    (fun s -> 
		       parameter_def_var (string_of_id s) c;
		       message ((string_of_id s) ^ " is assumed"))
		    sl)
               slcl
       | _ -> bad_vernac_args "PARAMETER")

let _ =
  add "Eval"
    (function
       | VARG_TACTIC_ARG (REDEXP (rn,unf)) :: VARG_COMMAND c :: g ->
           let (evmap,sign) = get_evmap_sign (goal_of_args g) in
           let redexp = redexp_of_ast evmap sign (rn,unf) in 
           let redfun = print_eval (reduction_of_redexp redexp evmap) sign in 
	   fun () -> mSG (redfun (fconstruct_with_univ evmap sign c))
       | _ -> bad_vernac_args "Eval")
    
let _ =
  add "Check"
    (function 
       | VARG_STRING kind :: VARG_COMMAND c :: g ->
	   let (evmap, sign) = get_evmap_sign (goal_of_args g) in
	   let prfun = match kind with
	     | "CHECK" -> print_val
             | "PRINTTYPE" -> print_type
             | _ -> anomaly "Unexpected string" 
	   in
	   (fun () -> mSG (prfun sign (fconstruct_with_univ evmap sign c)))
       | _ -> bad_vernac_args "Check")

let _ =
  add "PrintExtractId"
    (function 
       | [VARG_IDENTIFIER id] -> (fun () -> mSG(print_extracted_name id))
       | _ -> bad_vernac_args "PrintExtractId")

let _ =
  add "PrintExtract"
    (function 
       | [] -> (fun () -> mSG(print_extraction ()))
       | _  -> bad_vernac_args "PrintExtract")

let _ =
  add "SEARCH"
    (function 
       | [VARG_IDENTIFIER id] -> (fun () -> print_crible id)
       | _ -> bad_vernac_args "SEARCH")

let _ =
  add "INSPECT"
    (function 
       | [VARG_NUMBER n] -> (fun () -> mSG(inspect n))
       | _ -> bad_vernac_args "INSPECT")

let _ =
  add "SETUNDO"
    (function 
       | [VARG_NUMBER n] -> (fun () -> set_undo n)
       | _ -> bad_vernac_args "SETUNDO")

let _ =
  add "UNSETUNDO"
    (function 
       | [] -> (fun () -> unset_undo ())
       | _  -> bad_vernac_args "UNSETUNDO")

let _ =
  add "SETHYPSLIMIT"
    (function 
       | [VARG_NUMBER n] -> (fun () -> set_print_hyps_limit n)
       | _ -> bad_vernac_args "SETHYPSLIMIT")

let _ =
  add "UNSETHYPSLIMIT"
    (function 
       | [] -> (fun () -> unset_print_hyps_limit ())
       | _  -> bad_vernac_args "UNSETHYPSLIMIT")

let _ =
  add "ONEINDUCTIVE"
    (function 
       | [ VARG_STRING f;
           VARG_IDENTIFIER s;
           VARG_COMMAND c;
           VARG_BINDERLIST binders;
           VARG_BINDERLIST constructors ] ->
           let la = join_binders binders in
           let li = List.map
		      (function 
			 | ([id],c) -> (id,c)
			 | _ -> bad_vernac_args "ONEINDUCTIVE")
                      constructors
           in 
	   (fun () -> build_mutual la [(s,c,li)] (isfinite f))
       | _ -> bad_vernac_args "ONEINDUCTIVE")
    
let eq_la (id,ast) (id',ast') = id = id' & alpha_eq(ast,ast')

let extract_la_lc = function
  | []            -> anomaly "Vernacentries: empty list of inductive types"
  | (la,lc)::rest ->
      let rec check = function 
	| []             -> []
  	| (la',lc)::rest ->
            if (List.length la = List.length la') && 
               (List.for_all2 eq_la la la')
	    then 
	      lc::(check rest)
	    else 
	      error ("Parameters should be syntactically the same "^
		     "for each inductive type")
      in 
      (la,lc::(check rest))

let _ =
  add "MUTUALINDUCTIVE"
    (function 
       | [VARG_STRING f; VARG_VARGLIST indl] ->
	   let lac = 
	     (List.map 
          	(function 
		   | (VARG_VARGLIST 
			[VARG_IDENTIFIER arid;
			 VARG_COMMAND arc;
			 VARG_BINDERLIST binders; 
			 VARG_BINDERLIST lconstr])
		     ->
		       let la = join_binders binders in
          	       (la, (arid, arc,
			     List.map 
			       (function 
				  | ([id],c) -> (id,c)
				  | _ -> bad_vernac_args "")
			       lconstr))
		   | _ -> bad_vernac_args "MUTUALINDUCTIVE") indl)
	   in 
	   let (la,lnamearconstructs) = extract_la_lc lac in 
	   fun () -> build_mutual la lnamearconstructs (isfinite f)
       | _ -> bad_vernac_args "MUTUALINDUCTIVE")

let _ =
  add "OLDMUTUALINDUCTIVE"
    (function 
       | [VARG_BINDERLIST binders; VARG_STRING f; VARG_VARGLIST indl] ->
	   let la = join_binders binders in
           let lnamearconstructs = 
             (List.map 
           	(function 
		   | (VARG_VARGLIST 
			[VARG_IDENTIFIER arid;
			 VARG_COMMAND arc;
			 VARG_BINDERLIST lconstr])
		     -> (arid,
			 arc,
			 List.map 
			   (function 
			      | ([id],c) -> (id,c)
			      | _ -> bad_vernac_args "OLDMUTUALINDUCTIVE")
			   lconstr)
		   | _ -> bad_vernac_args "") indl)
	   in 
	   fun () -> build_mutual la lnamearconstructs (isfinite f)
       | _ -> bad_vernac_args "MUTUALINDUCTIVE")

let _ =
  add "RECORD"
    (function
       | [VARG_STRING coe;
          VARG_IDENTIFIER struc; 
          VARG_BINDERLIST binders; 
          VARG_COMMAND s; 
          VARG_VARGLIST namec; 
          VARG_VARGLIST cfs] -> 
           let ps = join_binders binders in
           let cfs = List.map
                       (function 
			  | (VARG_VARGLIST 
                               [VARG_STRING str;VARG_IDENTIFIER id;
                                VARG_COMMAND c]) ->
			      (str = "COERCION",(id,c))
			  | _ -> bad_vernac_args "RECORD")
                       cfs 
	   in
           let const = match namec with 
             | [] -> (id_of_string ("Build_"^(string_of_id struc)))
             | [VARG_IDENTIFIER id] -> id 
             | _ -> bad_vernac_args "RECORD"
           in 
	   fun () -> definition_structure (coe,struc,ps,cfs,const,s)
       | _ -> bad_vernac_args "RECORD")

let _ =
  add "MUTUALRECURSIVE"
    (function 
       | [VARG_VARGLIST lmi] -> 
	   (let lnameargsardef = 
	      List.map
		(function 
		   | (VARG_VARGLIST 
			[VARG_IDENTIFIER fid;
			 VARG_BINDERLIST farg; 
			 VARG_COMMAND arf;
			 VARG_COMMAND ardef])
		     -> (fid,join_binders farg,arf,ardef)
		   | _ -> bad_vernac_args "MUTUALRECURSIVE") lmi
	    in 
	    fun () -> build_recursive lnameargsardef)
       | _ -> bad_vernac_args "MUTUALRECURSIVE")

let _ =
  add "MUTUALCORECURSIVE"
    (function 
       | [VARG_VARGLIST lmi] -> 
	   let lnameardef = 
	     List.map
               (function 
		  | (VARG_VARGLIST 
		       [VARG_IDENTIFIER fid; 
			VARG_COMMAND arf;
			VARG_COMMAND ardef])
		    -> (fid,arf,ardef)
		  | _ -> bad_vernac_args "MUTUALCORECURSIVE") lmi
	   in 
	   fun () -> build_corecursive lnameardef
    |   _  -> bad_vernac_args "MUTUALCORECURSIVE")

let _ =
  add "INDUCTIONSCHEME"
    (function 
       | [VARG_VARGLIST lmi] -> 
	   let lnamedepindsort = 
	     List.map
	       (function 
		  | (VARG_VARGLIST 
		       [VARG_IDENTIFIER fid;
			VARG_STRING depstr;
			VARG_COMMAND ind; 
			VARG_COMMAND sort]) ->
		      let dep = match depstr with 
			| "DEP" -> true
                        | "NODEP" -> false
                        | _ -> anomaly "Unexpected string"
		      in 
		      (fid,dep,ind,sort)
		  | _ -> bad_vernac_args "INDUCTIONSCHEME") lmi
	   in 
	   fun () -> build_scheme lnamedepindsort
       | _ -> bad_vernac_args "INDUCTIONSCHEME")

let _ =
  add "SyntaxMacro"
    (function 
       | [VARG_IDENTIFIER id;VARG_COMMAND com] ->
	   (fun () -> 
	      syntax_definition id com;
              if not(is_silent()) then
                message ((string_of_id id) ^ " is now a syntax macro"))
       | [VARG_IDENTIFIER id;VARG_COMMAND com; VARG_NUMBER n] ->
           (fun () ->
              let rec aux t = function
                | 0 -> t
               	| n -> aux (ope("APPLIST",
                               	[t;ope("XTRA", [str "ISEVAR"])])) (n-1)
              in 
	      syntax_definition id (aux com n);
              if not(is_silent()) then
                message ((string_of_id id) ^ " is now a syntax macro"))
       | _ -> bad_vernac_args "SyntaxMacro")

let _ =
  add "ABSTRACTION"
    (function 
       | (VARG_IDENTIFIER id) :: (VARG_COMMAND com) :: l ->
	   (fun () ->
              let arity = 
		Array.of_list
		  (List.map (function | (VARG_NUMBER n) -> n
                               | _ -> bad_vernac_args "") l)
              in 
	      abstraction_definition id arity com;
              if (not(is_silent())) then
                message ((string_of_id id)^" is now an abstraction"))
       | _ -> bad_vernac_args "ABSTRACTION")

let _ =
  add "Require"
    (function 
       | [VARG_STRING import; VARG_STRING specif; VARG_IDENTIFIER id] ->
	   fun () -> 
	     without_mes_ambig 
	       (Library.require_module 
      		  (if specif="UNSPECIFIED" then 
		     None 
		   else 
		     Some (specif="SPECIFICATION"))
		  (string_of_id id) None)
      	       (import="IMPORT") 
       | _ -> bad_vernac_args "Require")

let _ =
  add "RequireFrom"
    (function 
       | [VARG_STRING import; VARG_STRING specif;
      	  VARG_IDENTIFIER id; VARG_STRING filename] ->
	   (fun () -> 
	      without_mes_ambig 
		(Library.require_module 
      		   (if specif="UNSPECIFIED" then 
		      None 
		    else 
		      Some (specif="SPECIFICATION"))
		   (string_of_id id) (Some filename))
		(import="IMPORT"))
       | _ -> bad_vernac_args "RequireFrom")

let _ =
  add "NOP"
    (function 
       | [] -> (fun () -> ())
       | _  -> bad_vernac_args "NOP")

let _ =
  add "CLASS"
    (function 
       | [VARG_STRING kind;VARG_IDENTIFIER id] -> 
	   let stre = 
	     if kind = "LOCAL" then 
	       make_strength(Library.cwd())
             else 
	       NeverDischarge 
	   in
	   fun () -> 
	     Class.try_add_new_class id stre;
             if (not (is_silent())) then
               message ((string_of_id id) ^ " is now a class")
       | _ -> bad_vernac_args "CLASS")
    
let _ =
  add "COERCION"
    (function 
       | [VARG_STRING kind;VARG_STRING identity;
          VARG_IDENTIFIER id;VARG_IDENTIFIER ids;VARG_IDENTIFIER idt] -> 
	   let stre = 
	     if (kind = "LOCAL") then 
	       make_strength(Library.cwd())
             else 
	       NeverDischarge 
	   in
	   let isid = identity = "IDENTITY" in
	   fun () -> 
	     Class.try_add_new_coercion (Some id) stre (Some (Left ids)) 
               (Some idt) isid;
             message ((string_of_id id) ^ " is now a coercion")
       | _ -> bad_vernac_args "COERCION")
 
let _ =
  add "PrintGRAPH"
    (function 
       | [] -> (fun () -> pPNL (Classops.print_graph()))
       | _  -> bad_vernac_args "PrintGRAPH")

let _ =
  add "PrintCLASSES"
    (function 
       | [] -> (fun () -> pPNL (Classops.print_classes()))
       | _  -> bad_vernac_args "PrintCLASSES")

let _ =
  add "PrintCOERCIONS"
    (function 
       | [] -> (fun () -> pPNL (Classops.print_coercions()))
       | _  -> bad_vernac_args "PrintCOERCIONS")

let _ =
  add "PrintPATH"
    (function 
       | [VARG_IDENTIFIER ids;VARG_IDENTIFIER idt] -> 
	   (fun () -> pPNL (Classops.print_path_between ids idt))
       | _ -> bad_vernac_args "PrintPATH")

(* Meta-syntax commands *)

let _ =
  add "TOKEN"
    (function
       | [VARG_STRING s] -> (fun () -> Metasyntax.add_token_obj s)
       | _ -> bad_vernac_args "TOKEN")

let _ =
  add "GRAMMAR"
    (function
       | [VARG_IDENTIFIER univ; VARG_ASTLIST al] ->
           (fun () -> Metasyntax.add_grammar_obj (string_of_id univ) al)
       | _ -> bad_vernac_args "GRAMMAR")

let _ =
  add "SYNTAX"
    (function
       | [VARG_IDENTIFIER whatfor; VARG_ASTLIST sel] ->
           (fun () -> Metasyntax.add_syntax_obj (string_of_id whatfor) sel)
       | _ -> bad_vernac_args "SYNTAX")
    
let _ =
  add "TacticDefinition"
    (function 
       | (VARG_IDENTIFIER na) :: (VARG_AST tacexp) :: idl ->
	   let ids = 
	     List.map 
               (function
                  | (VARG_IDENTIFIER id) -> (string_of_id id, Pcoq.ETast)
                  | _ -> bad_vernac_args "TacticDefinition") 
               idl
	   in 
	   fun () ->
             let body = Ast.to_act_check_vars ids Pcoq.ETast tacexp in  
	     Macros.add_macro_hint (string_of_id na) (List.map fst ids, body)
       | _ -> bad_vernac_args "TacticDefinition")

let _ =
  add "INFIX"
    (function
       | [VARG_AST assoc; VARG_NUMBER n; VARG_STRING inf; 
          VARG_IDENTIFIER pref] ->
           (fun () ->
              Metasyntax.add_infix
               	(Extend.gram_assoc assoc) n inf (string_of_id pref))
       | _ -> bad_vernac_args "INFIX")

let _ =
  add "DISTFIX"
    (function
       | [VARG_AST assoc; VARG_NUMBER n; VARG_STRING s; VARG_IDENTIFIER f] ->
           (fun () ->
              Metasyntax.add_distfix
               	(Extend.gram_assoc assoc) n s (string_of_id f))
       | _ -> bad_vernac_args "DISTFIX")

let _ =
  add "PrintGrammar"
    (function
       | [VARG_IDENTIFIER uni; VARG_IDENTIFIER ent] ->
           (fun () ->
              Metasyntax.print_grammar (string_of_id uni) (string_of_id ent))
       | _ -> bad_vernac_args "PrintGrammar")

(* Search commands *)

let _ =
  add "Searchisos"
  (function
     | [VARG_COMMAND c] -> 
	 (fun () ->
	    let cc=nf_betaiota (constr_of_com empty_evd (initial_sign()) c) in
            Searchisos.type_search cc)
     | _ -> bad_vernac_args "Searchisos")
    
open Options

let _ = 
  declare_async_int_option
    { optasynckey=SecondaryTable("Printing","Depth");
      optasyncname="the printing depth";
      optasyncread=Pp_control.get_depth_boxes;
      optasyncwrite=Pp_control.set_depth_boxes }

let _ =
  add "SetTableField"
    (function
       | [(VARG_IDENTIFIER t);(VARG_IDENTIFIER f);arg] -> 
	   (fun () ->
	      let key = 
		Options.SecondaryTable (string_of_id t,string_of_id f) in
	      match arg with
		| VARG_NUMBER n -> set_int_option_value key n
	 	| VARG_STRING s -> set_string_option_value key s
         	| _ -> error "No such type of option value")
       | [(VARG_IDENTIFIER t);(VARG_IDENTIFIER f)] -> 
	   (fun () ->
	      let key = 
		Options.SecondaryTable (string_of_id t,string_of_id f) in
	      set_bool_option_value key true)
       | [(VARG_IDENTIFIER t);arg] -> 
	   (fun () ->
	      let key = Options.PrimaryTable (string_of_id t) in
	      match arg with
		| VARG_NUMBER n -> set_int_option_value key n
	 	| VARG_STRING s -> set_string_option_value key s
         	| _ -> error "No such type of option value")
       | [(VARG_IDENTIFIER t)] -> 
	   (fun () ->
	      let key = Options.PrimaryTable (string_of_id t) in
	      set_bool_option_value key true)
       | _ -> bad_vernac_args "VernacOption")

let _ =
  add "UnsetTableField"
    (function
       | [(VARG_IDENTIFIER t);(VARG_IDENTIFIER f)] -> 
	   (fun () ->
	      let key = 
		Options.SecondaryTable (string_of_id t,string_of_id f) in
	      set_bool_option_value key false)
       | [(VARG_IDENTIFIER t)] -> 
	   (fun () ->
	      let key = Options.PrimaryTable (string_of_id t) in
	      set_bool_option_value key false)
       | _ -> bad_vernac_args "VernacOption")

let _ =
  add "AddTableField"
    (function
       | [VARG_IDENTIFIER t; VARG_IDENTIFIER f; VARG_IDENTIFIER v] -> 
	   (fun () ->
	      let key = 
		Options.SecondaryTable (string_of_id t,string_of_id f) in
	      try 
		(Options.get_option_table key)#add v
	      with Not_found -> 
		error_undeclared_key key)
       | [VARG_IDENTIFIER t; VARG_IDENTIFIER v] ->
	   (fun () ->
	      let key = Options.PrimaryTable (string_of_id t) in
	      try 
		x(Options.get_option_table key)#add v
	      with Not_found -> 
		error_undeclared_key key)
       | _ -> bad_vernac_args "TableField")

let _ =
  add "RemoveTableField"
    (function
       | [VARG_IDENTIFIER t; VARG_IDENTIFIER f; VARG_IDENTIFIER v] -> 
	   (fun () ->
	      let key = 
		Options.SecondaryTable (string_of_id t,string_of_id f) in
	      try 
		(Options.get_option_table key)#remove v
	      with Not_found -> 
		error_undeclared_key key)
       | [VARG_IDENTIFIER t; VARG_IDENTIFIER v] -> 
	   (fun () ->
	      let key = Options.PrimaryTable (string_of_id t) in
	      try 
		(Options.get_option_table key)#remove v
	      with Not_found -> 
		error_undeclared_key key)
  |  _ -> bad_vernac_args "TableField")
    
let _ =
  add "MemTableField"
    (function
       | [VARG_IDENTIFIER t; VARG_IDENTIFIER f; VARG_IDENTIFIER v] -> 
	   (fun () ->
	      let key = 
		Options.SecondaryTable (string_of_id t,string_of_id f) in
	      try 
		(Options.get_option_table key)#mem v
	      with Not_found -> 
		error_undeclared_key key)
       | [VARG_IDENTIFIER t; VARG_IDENTIFIER v] -> 
	   (fun () ->
	      let key = Options.PrimaryTable (string_of_id t) in
	      try 
		(Options.get_option_table key)#mem v
	      with Not_found -> 
		error_undeclared_key key)
       |  _ -> bad_vernac_args "TableField")

let _ =
  add "PrintOption"
  (function
     | [VARG_IDENTIFIER t; VARG_IDENTIFIER f] -> 
	 (fun () ->
	    let key = Options.SecondaryTable (string_of_id t,string_of_id f) in
	    try 
	      (Options.get_option_table key)#print
	    with not_found ->
              try 
		Options.print_option_value key
              with Not_found -> 
		error_undeclared_key key)
     | [VARG_IDENTIFIER t] -> 
	 (fun () ->
	    let key = Options.PrimaryTable (string_of_id t) in
	    try 
	      (Options.get_option_table key)#print
	    with not_found ->
              try 
		Options.print_option_value key
              with Not_found -> 
	  	if (string_of_id t) = "Tables" then 
		  Options.print_tables ()
	  	else 
		  mSG(Pretty.print_name t))
     | _ -> bad_vernac_args "TableField")

(*Only for debug*)

let _ =
  add "PrintConstr"
    (function
       | [VARG_COMMAND c] -> 
	   (fun () ->
	      Term.constr_display (constr_of_com empty_evd (initial_sign()) c))
       | _ -> bad_vernac_args "PrintConstr")
