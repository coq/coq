(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(* Concrete syntax of the mathematical vernacular MV V2.6 *)

open Declarations
open Mod_declarations
open Pp
open Util
open Options
open System
open Identifier
open Names
open Term
open Pfedit
open Tacmach
open Proof_trees
open Proof_type
open Tacred
open Environ
open Vernacinterp
open Coqast
open Ast
open Astterm
open Astmod
open Prettyp
open Printer
open Tacinterp
open Tactic_debug
open Command
open Goptions
open Declare

(* Dans join_binders, s'il y a un "?", on perd l'info qu'il est partag� *)
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
  msgnl(Refiner.print_script true evc (Global.named_context()) pf)

let show_prooftree () =
  let pts = get_pftreestate () in
  let pf = proof_of_pftreestate pts
  and evc = evc_of_pftreestate pts in
  msg(Refiner.print_proof evc (Global.named_context()) pf)

let show_open_subgoals () =
  let pfts = get_pftreestate () in
  msg(pr_subgoals_of_pfts pfts)

let show_nth_open_subgoal n =
  let pf = proof_of_pftreestate (get_pftreestate ()) in
  msg(pr_subgoal n (fst(frontier pf)))

let show_open_subgoals_focused () =
  let pfts = get_pftreestate () in
  match focus() with
    | 0 -> 
	msg(pr_subgoals_of_pfts pfts)
    | n -> 
	let pf = proof_of_pftreestate pfts in
	let gls = fst(frontier pf) in 
	if n > List.length gls then 
	  (make_focus 0; msg(pr_subgoals_of_pfts pfts))
	else if List.length gls < 2 then 
	  msg(pr_subgoal n gls)
	else 
	  msg (v 0 (**)(  int(List.length gls) ++ str" subgoals" ++ cut () ++ 
		      pr_subgoal n gls  )(**))

let show_node () =
  let pts = get_pftreestate () in
  let pf = proof_of_pftreestate pts
  and cursor = cursor_of_pftreestate pts in
  msg ( prlist_with_sep pr_spc pr_int (List.rev cursor) ++ fnl () ++
         prgl pf.goal ++ fnl () ++
         (match pf.ref with
            | None -> str"BY <rule>"
            | Some(r,spfl) ->
		(  str"BY " ++ Refiner.pr_rule r ++ fnl () ++ str"  " ++
		   hov 0 (prlist_with_sep pr_fnl prgl
			    (List.map (fun p -> p.goal) spfl))  ))++
         fnl () )
    
let show_top_evars () =
  let pfts = get_pftreestate () in 
  let gls = top_goal_of_pftreestate pfts in 
  let sigma = project gls in 
  msg (pr_evars_int 1 (Evd.non_instantiated sigma))

(* Locate commands *)
let locate_qualid loc qid =
  try Nametab.locate qid
  with Not_found -> 
  try
    let _ = Syntax_def.locate_syntactic_definition qid in
    error
      ("Unexpected reference to a syntactic definition: "
       ^(Libnames.string_of_qualid qid))
  with Not_found ->
    Nametab.error_global_not_found_loc loc qid

 (* Pour pcoq *)
let global = locate_qualid

let locate_file f =
  try
    let _,file =
      System.where_in_path (Library.get_load_path()) f in
    msg (**)(  str file ++ fnl ()  )(**)
  with Not_found -> 
    msg (hov 0 (**)(  str"Can't find file" ++ spc () ++ str f ++ spc () ++
		  str"on loadpath" ++ fnl ()  )(**))

let print_located_qualid qid =
  try
    let ref = Nametab.locate qid in
    msg
      (**)(  str (Libnames.string_of_qualid (Nametab.get_full_qualid ref)) ++ fnl ()  )(**)
  with Not_found -> 
  try
    msg
      (**)(  str (Libnames.string_of_path (Syntax_def.locate_syntactic_definition qid)) ++
	 fnl ()  )(**)
  with Not_found ->
    error ((Libnames.string_of_qualid qid) ^ " not a defined object")

let print_path_entry (s,l) =
  (**)(  str s ++ tbrk (0,2) ++ str (string_of_dirpath l)  )(**)

let print_loadpath () =
  let l = Library.get_full_load_path () in
  msgnl (Pp.t (**)(  str "Physical path:                                 " ++
		 tab () ++ str "Logical Path:" ++ fnl () ++ 
		 prlist_with_sep pr_fnl print_path_entry l  )(**))

let get_current_context_of_args = function
  | [VARG_NUMBER n] -> get_goal_context n
  | [] -> get_current_context ()
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

let msg_found_library = function
  | Library.LibLoaded, fulldir, file ->
      msg (**)(  pr_dirpath fulldir ++ str " has been loaded from file" ++ fnl () ++
      str file ++ fnl ()  )(**)
  | Library.LibInPath, fulldir, file ->
      msg (**)(  pr_dirpath fulldir ++ str " is bound to file " ++ str file ++ fnl ()  )(**)

let msg_notfound_library qid = function
  | Library.LibUnmappedDir ->
      let dir = fst (Libnames.repr_qualid qid) in
      msg (**)(  str "No physical path is bound to " ++ pr_dirpath dir ++ fnl ()  )(**)
  | Library.LibNotFound ->
      msg (hov 0 
	(**)(  str"Unable to locate library" ++ spc () ++ Libnames.pr_qualid qid ++ fnl ()  )(**))
  | _ -> assert false

let _ = 
  add "LocateLibrary"
    (function 
       | [VARG_QUALID qid] ->
	   (fun () ->
	     try msg_found_library (Library.locate_qualified_library qid)
	     with e -> msg_notfound_library qid e)
       | _ -> bad_vernac_args "LocateLibrary")

let _ = 
  add "Locate"
    (function 
       | [VARG_QUALID qid] -> (fun () -> print_located_qualid qid)
       | _  -> bad_vernac_args "Locate")

(* For compatibility *)
let _ = 
  add "ADDPATH"
    (function 
       | [VARG_STRING dir] ->
	   (fun () -> Mltop.add_path dir Nametab.default_root_prefix)
       | [VARG_STRING dir ; VARG_QUALID alias] ->
           let aliasdir,aliasname = Libnames.repr_qualid alias in
	   (fun () -> Mltop.add_path dir (aliasdir@[aliasname]))
       | _ -> bad_vernac_args "ADDPATH")

(* For compatibility *)
let _ =
  add "DELPATH"
    (function 
       | [VARG_STRING dir] -> (fun () -> Library.remove_path dir)
       | _ -> bad_vernac_args "DELPATH")

let _ = 
  add "RECADDPATH"
    (function 
       | [VARG_STRING dir] ->
	   (fun () -> Mltop.add_rec_path dir Nametab.default_root_prefix)
       | [VARG_STRING dir ; VARG_QUALID alias] ->
           let aliasdir,aliasname = Libnames.repr_qualid alias in
	    (fun () -> Mltop.add_rec_path dir (aliasdir@[aliasname]))
       | _ -> bad_vernac_args "RECADDPATH")

(* For compatibility *)
let _ = 
  add "PrintPath"
    (function 
       | [] -> (fun () -> print_loadpath ())
       | _  -> bad_vernac_args "PrintPath")

let _ =
  add "PWD"
    (function 
       | [] -> (fun () -> print_endline (Sys.getcwd()))
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
              if_verbose print_endline (Sys.getcwd()))
       | [] -> (fun () -> if_verbose print_endline (Sys.getcwd()))
       | _  -> bad_vernac_args "CD")

(* Managing states *)

let abort_refine f x =
  if Pfedit.refining() then delete_all_proofs ();
  f x
  (* used to be: error "Must save or abort current goal first" *)

let _ =
  add "WriteState"
    (function 
       | [VARG_STRING file] ->
	   (fun () -> abort_refine States.extern_state file)
       | [VARG_IDENTIFIER id] ->
	   let file = string_of_id id in
	   (fun () -> abort_refine States.extern_state file)
       | _ -> bad_vernac_args "SaveState")

let _ =
  add "RestoreState"
    (function 
       | [VARG_STRING file] ->
	   (fun () -> abort_refine States.intern_state file)
       | [VARG_IDENTIFIER id] ->
	   let file = string_of_id id in
	   (fun () -> abort_refine States.intern_state file)
       | _ -> bad_vernac_args "LoadState")

(* Resetting *)

let _ =
  add "ResetName"
    (function 
       | [VARG_IDENTIFIER id] -> 
	   (fun () -> abort_refine Lib.reset_name id)
       | _ -> bad_vernac_args "ResetName")

let _ =
  add "ResetInitial"
    (function 
       | [] -> (fun () -> abort_refine Lib.reset_initial ())
       | _  -> bad_vernac_args "ResetInitial")

(***
let _ =
  add "ResetSection"
    (function 
       | [VARG_IDENTIFIER id] ->
	   (fun () -> reset_section (string_of_id id))
       | _ -> bad_vernac_args "ResetSection")

***)

(* Real Modules *)

let _ = 
  add "BeginMod"
    (function
       | (VARG_IDENTIFIER id)::tl ->
	   let args_ast,tl = match tl with
	     | (VARG_BINDERLIST args) :: tl -> args,tl
	     | tl -> [], tl
	   in
	   let res_ast_opt = match tl with
	     | [] -> None
	     | [VARG_MODTYPE res] -> Some res
	     | _ -> bad_vernac_args "BeginMod"
	   in
	     (fun () -> 
		let l = label_of_ident id (* args, res - option *) in
		let argids = list_map_append fst args_ast in
		  match res_ast_opt with 
		    | Some res_ast -> 
			let args, res = interp_modtype Evd.empty (Global.env()) 
					  args_ast res_ast
			in
			  Declaremods.begin_module l argids args (Some res)
		    | None ->
			let args = interp_modbinders Evd.empty (Global.env()) 
				     args_ast
			in
			  Declaremods.begin_module l argids args None)
	     
       | _ -> bad_vernac_args "BeginMod")

let _ = 
  add "Module"
    (function 
       | (VARG_IDENTIFIER id)::tl ->
	   let args_ast,tl = match tl with
	     | (VARG_BINDERLIST args) :: tl -> args,tl
	     | tl -> [], tl
	   in
	   let res_ast_opt, tl = match tl with
	     | (VARG_MODTYPE res)::tl -> Some res,tl
	     | tl -> None,tl
	   in
	   let me_ast_opt, tl = match tl with (* for future Module M. in signatures *)
	     | (VARG_MODEXPR ast)::tl -> Some ast, tl
	     | tl -> None, tl
	   in
	     (match tl with [] -> () | _::_ -> bad_vernac_args "Module");
	     (match me_ast_opt, res_ast_opt with 
		| None, None -> bad_vernac_args "Module"
		| _ -> ());
	     (fun () -> 
		let l = label_of_ident id (* args, res - option *) in
		let argids = list_map_append fst args_ast in
		let args,me_body_opt = 
		  interp_modexpr Evd.empty (Global.env()) 
		    args_ast me_ast_opt
		in
		let me_opt = 
		  option_app
		    (List.fold_right 
		       (fun (mbid,mte) me -> MEfunctor(mbid,mte,me))
		       args)
		    me_body_opt
		in
		let res_opt = 
		  option_app 
		    (fun res_ast -> 
		       snd 
		         (interp_modtype Evd.empty (Global.env()) [] res_ast)
		    ) 
		    res_ast_opt
		in
		let mte_opt = 
		  option_app
		    (List.fold_right 
		       (fun (arg_id,arg_t) mte -> 
			  MTEfunsig(arg_id,arg_t,mte))
		       args)
		    res_opt
		in
		let mod_entry = 
		  {mod_entry_type = mte_opt;
		   mod_entry_expr = me_opt}
		in
		  Declaremods.declare_module l mod_entry)
	     
       | _ -> bad_vernac_args "Module")

let _ =
  add "EndMod"
    (function
       | [VARG_IDENTIFIER id] ->
	   let l = label_of_ident id in 
	     (fun () -> Declaremods.end_module l)
       | _ -> bad_vernac_args "EndMod")


let _ =
  add "ImportMod"
    (function
       | [VARG_QUALID qid] ->
	   let mp = Nametab.locate_module qid in
	     (fun () -> Declaremods.import_module mp)
       | _ -> bad_vernac_args "ImportMod")

let _ = 
  add "BeginModtype"
    (function
       | (VARG_IDENTIFIER id)::tl ->
	   let args_ast,tl = match tl with
	     | (VARG_BINDERLIST args) :: tl -> args,tl
	     | tl -> [], tl
	   in
	     (match tl with _::_ -> bad_vernac_args "EndMod" | [] -> ());
	     (fun () -> 
		let l = label_of_ident id in
		let argids = list_map_append fst args_ast in
		let args = interp_modbinders Evd.empty (Global.env()) 
			     args_ast
		in
		  Declaremods.begin_modtype l argids args)
       | _ -> bad_vernac_args "BeginModtype")

let _ =
  add "EndModtype"
    (function
       | [VARG_IDENTIFIER id] ->
	   let l = label_of_ident id in 
	     fun () -> Declaremods.end_modtype l
       | _ -> bad_vernac_args "EndModtype")




(* Compilation Units *)

let _ =
  add "BeginModule"
    (function 
       | [VARG_IDENTIFIER id] ->
	   let s = string_of_id id in
	   let lpe,_ = System.find_file_in_path (Library.get_load_path ()) (s^".v") in
	   let dir = (Library.find_logical_path lpe) @ [id] in
	   fun () ->
	     Lib.start_comp_unit dir
       | _ -> bad_vernac_args "BeginModule")

let _ =
  add "WriteModule"
    (function 
       | [VARG_IDENTIFIER id] ->
	   let mid = Lib.comp_unit_name id in
	   fun () -> Library.save_module_to mid (string_of_id id)
       | [VARG_IDENTIFIER id; VARG_STRING f] ->
	   let mid = Lib.comp_unit_name id in
	   fun () -> Library.save_module_to mid f
       | _ -> bad_vernac_args "WriteModule")

let _ =
  add "ReadModule"
    (function 
       | [VARG_QUALID qid] ->
	   fun () -> without_mes_ambig Library.read_module qid
       | _ -> bad_vernac_args "ReadModule")

let _ =
  add "ImportModule"
    (function 
       | [VARG_QUALID qid] ->
	   fun () ->
	     let fullname = Nametab.locate_loaded_library qid in 
	     without_mes_ambig Library.import_module fullname
       | _ -> bad_vernac_args "ImportModule")

let _ =
  add "PrintModules"
    (function 
       | [] -> 
	   (fun () ->
              let opened = Library.opened_modules ()
	      and loaded = Library.loaded_modules () in
              msg (**)(  str"Loaded Modules: " ++
		     hov 0 (prlist_with_sep pr_fnl pr_dirpath loaded) ++
		     fnl () ++
		     str"Imported (open) Modules: " ++
		     hov 0 (prlist_with_sep pr_fnl pr_dirpath opened) ++ 
		     fnl ()  )(**))
       | _ -> bad_vernac_args "PrintModules")

(* Sections *)

let _ =
  add "BeginSection"
    (function 
       | [VARG_IDENTIFIER id] ->
	   (fun () -> let _ = Lib.open_section id in ())
       | _ -> bad_vernac_args "BeginSection")

let _ =
  add "EndSection"
    (function 
       | [VARG_IDENTIFIER id] ->
	   (fun () ->
	      check_no_pending_proofs ();
              Discharge.close_section (is_verbose ()) id)
       | _ -> bad_vernac_args "EndSection")

(* Proof switching *)

let _ =
  add "GOAL"
    (function 
       | [VARG_CONSTR com] ->
	   (fun () ->
              if not (refining()) then begin
              	start_proof_com None Declare.NeverDischarge com;
		if_verbose show_open_subgoals ()
              end else 
		error "repeated Goal not permitted in refining mode")
       | [] -> (fun () -> ())
       | _  -> bad_vernac_args "GOAL")

let _ = add "Comments" (function _ -> (fun () -> ()))

let _ =
  add "ABORT"
    (function 
       | [VARG_IDENTIFIER id] -> 
	   (fun () -> 
	      delete_proof id;
	      message ("Goal "^(string_of_id id)^" aborted"))
       | [] -> (fun () -> 
		  delete_current_proof ();
		  message "Current goal aborted")
       | _  -> bad_vernac_args "ABORT")

let _ =
  add "ABORTALL"
    (function 
       | [] -> (fun () ->
		  if refining() then begin
		    delete_all_proofs ();
		    message "Current goals aborted"
		  end else
		    error "No proof-editing in progress")

       | _  -> bad_vernac_args "ABORTALL")

let _ =
  add "RESTART"
    (function 
       | [] -> (fun () -> (restart_proof();show_open_subgoals ()))
       | _  -> bad_vernac_args "RESTART")

let _ =
  add "SUSPEND"
    (function 
       | [] -> (fun () -> suspend_proof ())
       | _  -> bad_vernac_args "SUSPEND")

let _ =
  add "RESUME"
    (function 
       | [VARG_IDENTIFIER id] ->
	   (fun () -> resume_proof id)
       | [] -> (fun () -> resume_last_proof ())
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
       | [] -> (fun () -> Impargs.make_implicit_args true)
       | _  -> bad_vernac_args "IMPLICIT_ARGS_ON")

let _ =
  add "IMPLICIT_ARGS_OFF"
    (function 
       | [] -> (fun () -> Impargs.make_implicit_args false)
       | _  -> bad_vernac_args "IMPLICIT_ARGS_OFF")

let _ =
  add "TEST_IMPLICIT_ARGS"
    (function 
       | [] ->
	   (fun () ->
	      if Impargs.is_implicit_args () then
		message "Implicit arguments mode is set"
	      else 
		message "Implicit arguments mode is unset")
       | _  -> bad_vernac_args "IMPLICIT_ARGS_OFF")

let coercion_of_qualid loc qid =
  let ref = locate_qualid loc qid in
  let coe = Classops.coe_of_reference ref in
  if not (Classops.coercion_exists coe) then
    errorlabstrm "try_add_coercion" 
      (**)(  Printer.pr_global ref ++ str" is not a coercion"  )(**);
  coe

let _ =
  add "PRINTING_COERCIONS_ON"
    (function 
       | [] -> (fun () -> Termast.print_coercions := true)
       | l ->
	   let ql =
	     List.map 
	       (function
		  | VARG_QUALID qid -> qid
		  | _ ->  bad_vernac_args "PRINTING_COERCIONS_ON") l in
	   (fun () ->
	      List.iter
		(fun qid ->
		   Classops.set_coercion_visibility true
		     (coercion_of_qualid dummy_loc qid))
		ql))

let _ =
  add "PRINTING_COERCIONS_OFF"
    (function 
       | [] -> (fun () -> Termast.print_coercions := false)
       | l -> 
	   let ql =
	     List.map 
	       (function
		  | VARG_QUALID qid -> qid
		  | _ ->  bad_vernac_args "PRINTING_COERCIONS_OFF") l in
	   (fun () ->
	      List.iter
		(fun qid ->
		   Classops.set_coercion_visibility false 
		     (coercion_of_qualid dummy_loc qid))
		ql))

let _ =
  add "TEST_PRINTING_COERCIONS"
    (function 
       | [] ->
           (fun () ->
              if !(Termast.print_coercions) = true then
		message "Printing of coercions is set"
              else 
		message "Printing of coercions is unset")
       | l -> 
	   let ql =
	     List.map 
	       (function
		  | VARG_QUALID qid -> qid
		  | _  -> bad_vernac_args "TEST_PRINTING_COERCIONS") l in
	   (fun () ->
              List.iter
		(fun qid ->
		   let coe = coercion_of_qualid dummy_loc qid in
	           if Classops.is_coercion_visible coe then
		     message
		       ("Printing of coercion "^(Libnames.string_of_qualid qid)^
			" is set")
		   else 
		     message 
		       ("Printing of coercion "^(Libnames.string_of_qualid qid)^
			" is unset"))
		ql))
    
let number_list = 
  List.map (function VARG_NUMBER n -> n | _ -> bad_vernac_args "Number list") 

let _ =
  add "IMPLICITS"
    (function 
       | (VARG_STRING "") :: (VARG_QUALID qid) :: l -> 
	   (fun () ->
	      let imps = number_list l in
	      Impargs.declare_manual_implicits
		(locate_qualid dummy_loc qid) imps)
       | [VARG_STRING "Auto"; VARG_QUALID qid] -> 
	   (fun () -> 
	      Impargs.declare_implicits (locate_qualid dummy_loc qid))
       | _  -> bad_vernac_args "IMPLICITS")

let interp_definition_kind = function
  | "THEOREM" -> (NeverDischarge,     true)
  | "LEMMA"   -> (NeverDischarge,     true)
  | "FACT"    -> (make_strength_1 (), true)
  | "REMARK"  -> (make_strength_0 (), true)
  | "DEFINITION" -> (NeverDischarge,     false)
  | "LET"        -> (make_strength_1 (), false)
  | "LETTOP"     -> (NeverDischarge,     false)
  | "LOCAL"      -> (make_strength_0 (), false)
  | _       -> anomaly "Unexpected definition kind"

let _ =
  add "SaveNamed"
    (function 
       | [] -> 
	   (fun () -> if_verbose show_script (); save_named true)
       | _ -> bad_vernac_args "SaveNamed")

let _ =
  add "DefinedNamed"
    (function 
       | [] -> 
	   (fun () -> if_verbose show_script (); save_named false)
       | _ -> bad_vernac_args "DefinedNamed")

let _ =
  add "DefinedAnonymous"
    (function 
       | [VARG_IDENTIFIER id] -> 
	   (fun () -> 
	      if_verbose show_script ();
              save_anonymous false id)
       | _ -> bad_vernac_args "DefinedAnonymous")

let _ =
  add "SaveAnonymous"
    (function 
       | [VARG_STRING kind; VARG_IDENTIFIER id] -> 
	   (fun () -> 
	      let (strength, opacity) = interp_definition_kind kind in
	      if_verbose show_script ();
              save_anonymous_with_strength strength opacity id)
       | [VARG_IDENTIFIER id] -> 
	   (fun () -> 
	      if_verbose show_script ();
              save_anonymous true id)
       | _ -> bad_vernac_args "SaveAnonymous")

let _ =
  add "TRANSPARENT"
    (fun id_list () ->
       List.iter 
	 (function 
	    | VARG_CONSTANT sp -> Global.set_transparent sp
	    |   _  -> bad_vernac_args "TRANSPARENT")
	 id_list)

let warning_opaque s =
  if_verbose warning
      ("This command turns the constants which depend on the definition/proof
of "^s^" un-re-checkable until the next \"Transparent "^s^"\" command.")

let _ =
  add "OPAQUE"
    (fun id_list () ->
       List.iter
	 (function 
	    | VARG_CONSTANT sp ->
		warning_opaque (Libnames.string_of_qualid (Nametab.get_short_qualid (ConstRef sp)));
		Global.set_opaque sp
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
       | [] -> (fun () -> Impargs.implicitely show_open_subgoals ())
       | [VARG_NUMBER n] -> 
	   (fun () -> Impargs.implicitely show_nth_open_subgoal n)
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
	   (fun () -> (Pfedit.traverse n;show_node()))
       | [VARG_STRING"top"] ->
           (fun () -> (Pfedit.reset_top_of_tree ();show_node()))
       | [VARG_STRING"next"] ->
           (fun () -> (Pfedit.traverse_next_unproven ();show_node()))
       | [VARG_STRING"prev"] ->
           (fun () -> (Pfedit.traverse_prev_unproven ();show_node()))
       | _ -> bad_vernac_args "Go")

let _ =
  add "ShowProof"
    (function 
       | [] ->
	   (fun () ->
	      let pts = get_pftreestate () in
	      let pf = proof_of_pftreestate pts in
	      let cursor = cursor_of_pftreestate pts in
	      let evc = evc_of_pftreestate pts in
	      let (pfterm,meta_types) = extract_open_pftreestate pts in
	      msgnl ( str"LOC: " ++
		       prlist_with_sep pr_spc pr_int (List.rev cursor) ++ fnl () ++
		       str"Subgoals" ++ fnl () ++
		       prlist
			 (fun (mv,ty) -> 
			    (**)(  int mv  ++ str" -> "  ++ prtype ty  ++ fnl ()  )(**))
			 meta_types++
		       str"Proof: " ++ prterm (Evarutil.nf_evar evc pfterm) ))
       | _ -> bad_vernac_args "ShowProof")

let _ =
  add "CheckGuard"
    (function 
       | [] ->
	   (fun () ->
	      let pts = get_pftreestate () in
	      let pf = proof_of_pftreestate pts 
	      and cursor = cursor_of_pftreestate pts in
	      let (pfterm,_) = extract_open_pftreestate pts in
	      let message = 
		try 
		  Typeops.control_only_guard (Evarutil.evar_env pf.goal)
		    Evd.empty pfterm; 
		  (**)(  str "The condition holds up to here"  )(**)
                with UserError(_,s) -> 
		  (**)(  str ("Condition violated : ")  ++s  )(**)
	      in 
	      msgnl message)
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
       let l = number_list l in
       fun () ->
         let pts = get_pftreestate() in
         let evc = evc_of_pftreestate pts in
         let rec aux pts = function
           | [] -> pts
           | (n::l) -> aux (Tacmach.traverse n pts) l in 
         let pts = aux pts (l@[-1]) in
         let pf = proof_of_pftreestate pts in 
	 msg (Refiner.print_script true evc (Global.named_context()) pf))

let _ =
  add "ExplainProofTree"
    (function l ->
       let l = number_list l in 
       fun () ->
         let pts = get_pftreestate() in
         let evc = evc_of_pftreestate pts in
         let rec aux pts = function
           | [] -> pts
           | (n::l) -> aux (Tacmach.traverse n pts) l in 
         let pts = aux pts (l@[-1]) in
         let pf = proof_of_pftreestate pts in 
	 msg (Refiner.print_proof evc (Global.named_context()) pf))

let _ =
  add "ShowProofs"
    (function [] ->
       (fun () ->
	  let l = Pfedit.get_all_proof_names() in 
	  msgnl (prlist_with_sep pr_spc pr_id l))
       | _  -> bad_vernac_args "ShowProofs")

let _ =
  add "PrintAll"
    (function 
       | [] -> (fun () -> msg(print_full_context_typ ()))
       | _  -> bad_vernac_args "PrintAll")

let _ =
  add "PRINT"
    (function 
       | [] -> (fun () -> msg(print_local_context()))
       | _  -> bad_vernac_args "PRINT")

(* Pris en compte dans PrintOption *)

let _ =
  add "PrintId"
    (function 
       | [VARG_QUALID qid] -> (fun () -> msg(print_name qid))
       | _ -> bad_vernac_args "PrintId")

let _ =
  add "PrintOpaqueId"
    (function 
       | [VARG_QUALID qid] -> (fun () -> msg(print_opaque_name qid))
       | _ -> bad_vernac_args "PrintOpaqueId")

let _ =
  add "PrintSec"
    (function 
       | [VARG_QUALID qid] -> (fun () -> msg(print_sec_context_typ qid))
       | _ -> bad_vernac_args "PrintSec")

let _ = declare_async_bool_option 
	  {optasyncname  = "Silent";
	   optasynckey   = (PrimaryTable "Silent");
	   optasyncread  = is_silent;
	   optasyncwrite = make_silent }

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
  add "DebugOn"
    (function 
       | [] -> (fun () -> set_debug DebugOn)
       | _  -> bad_vernac_args "DebugOn")

let _ =
  add "DebugOff"
    (function 
       | [] -> (fun () -> set_debug DebugOff)
       | _  -> bad_vernac_args "DebugOff")

let _ =
  add "StartProof"
    (function 
       | [VARG_STRING kind;VARG_IDENTIFIER s;VARG_CONSTR com] ->
	   let stre = fst (interp_definition_kind kind) in
	   fun () ->
             begin
               if (kind = "LETTOP") && not(refining ()) then
                 errorlabstrm "Vernacentries.StartProof" (**)(  str
                 "Let declarations can only be used in proof editing mode"  )(**);
               start_proof_com (Some s) stre com;
               if_verbose show_open_subgoals ()
             end
       | _ -> bad_vernac_args "StartProof")

let _ =
  add "TheoremProof"
    (function 
       | [VARG_STRING kind; VARG_IDENTIFIER id;
	  VARG_CONSTR com; VARG_VARGLIST coml] ->
	   let calls = List.map
			 (function 
			    | (VCALL(na,l)) -> (na,l)
			    | _ -> bad_vernac_args "")
			 coml 
	   in
	   let (stre,opacity) = interp_definition_kind kind in
           (fun () ->
              try
            	States.with_heavy_rollback
		  (fun () ->
                     start_proof_com (Some id) stre com;
                     if_verbose show_open_subgoals ();
                     List.iter Vernacinterp.call calls;
                     if_verbose show_script ();
                     if not (kind = "LETTOP") then
                       save_named opacity
                     else
                       let csr = interp_type Evd.empty (Global.env ()) com
                       and (_,({const_entry_body = opft;
                                const_entry_type = _},_)) = cook_proof () in
			 match opft with
			   | None -> anomaly "empty constant body"
			   | Some pft -> 
			       let cutt = vernac_tactic ("Cut",[Constr csr])
			       and exat = vernac_tactic ("Exact",[Constr pft]) in
				 delete_proof id;
				 by (tclTHENS cutt [introduction id;exat]))
		  ()
              with e ->
            	if (is_unsafe "proof") && not (kind = "LETTOP") then begin
                  msgnl (**)(  str "Warning: checking of theorem " ++ pr_id id ++
                           spc () ++ str "failed" ++
                           str "... converting to Axiom"  )(**);
                  delete_proof id;
                  let _ = parameter_def_var id com in ()
           	end else 
		  errorlabstrm "Vernacentries.TheoremProof"
                    (**)(  str "checking of theorem " ++ pr_id id ++ spc () ++
                       str "failed... aborting"  )(**))
       | _ -> bad_vernac_args "TheoremProof")

let _ =
  add "DEFINITION"
    (function 
       | (VARG_STRING kind :: VARG_IDENTIFIER id :: VARG_CONSTR c :: rest) ->
	   let typ_opt,red_option = match rest with
	     | [] -> None, None
	     | [VARG_CONSTR t] -> Some t, None
	     | [VARG_TACTIC_ARG (Redexp redexp)] ->
		 None, Some redexp
	     | [VARG_CONSTR t; VARG_TACTIC_ARG (Redexp redexp)] ->
		 Some t, Some redexp
	     | _ -> bad_vernac_args "DEFINITION"
	   in 
	   let local,stre,coe,objdef,idcoe = match kind with
	     | "DEFINITION" -> false,NeverDischarge,   false,false,false
             | "COERCION" ->   false,NeverDischarge,   true, false,false
             | "LCOERCION" ->  true, make_strength_0(),true, false,false
             | "LET" ->        true, make_strength_2(),false,false,false
             | "LOCAL" ->      true, make_strength_0(),false,false,false
             | "OBJECT" ->     false,NeverDischarge,   false,true, false
             | "LOBJECT" ->    true, make_strength_0(),false,true, false
             | "OBJCOERCION" -> false,NeverDischarge,  true, true, false
             | "LOBJCOERCION" -> true,make_strength_0(),true,true, false
             | "SUBCLASS" ->   false,NeverDischarge,   false,false,true
             | "LSUBCLASS" ->  true, make_strength_0(),false,false,true
             | _       -> anomaly "Unexpected string"
	   in 
	   fun () ->
	     let ref =
	       definition_body_red red_option id (local,stre) c typ_opt in
             if coe then begin
	       Class.try_add_new_coercion ref stre;
               if_verbose message ((string_of_id id) ^ " is now a coercion")
	     end;
	     if idcoe then begin
	       let cl = Class.class_of_ref ref in
	       Class.try_add_new_coercion_subclass cl stre
	     end;
             if objdef then Recordobj.objdef_declare ref
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
	   let stre = make_strength_0() in
	   fun () ->
	     List.iter 
	       (fun (sl,c) -> 
		  List.iter 
		    (fun id ->
                       let ref = hypothesis_def_var (refining()) id stre c in
                       if coe then Class.try_add_new_coercion ref stre)
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
		       let _ = parameter_def_var s c in ())
		    sl)
               slcl
       | _ -> bad_vernac_args "PARAMETER")

let _ =
  add "Eval"
    (function
       | VARG_TACTIC_ARG (Redexp redexp) :: VARG_CONSTR c :: g ->
           let (evmap,sign) = get_current_context_of_args g in
           let redfun = print_eval (reduction_of_redexp redexp) sign in 
	   fun () -> msg (redfun (judgment_of_rawconstr evmap sign c))
       | _ -> bad_vernac_args "Eval")

let _ =
  add "Check"
    (function 
       | VARG_STRING "PRINTTYPE" :: VARG_CONSTR c :: _ ->
           (fun () ->
              let evmap = Evd.empty in
              let env = Global.env() in
              let c = interp_constr evmap env c in
              let senv = Global.safe_env() in
              let j = Safe_env.typing senv c in
              msg (print_safe_judgment env j))
       | VARG_STRING "CHECK" :: VARG_CONSTR c :: g ->
	   (fun () ->
	      let (evmap, env) = get_current_context_of_args g in
              let c = interp_constr evmap env c in
              let j = Safe_env.typing_in_unsafe_env env c in
              msg (print_judgment env j))
       | _ -> bad_vernac_args "Check")
    

let extract_qualid = function 
  | VARG_QUALID qid ->
      (try Nametab.locate_loaded_library qid
       with Not_found -> 
	 error ("Module/section "^(Libnames.string_of_qualid qid)^" not found"))
  | _ -> bad_vernac_args "extract_qualid"

let inside_outside = function
  | (VARG_STRING "outside") :: l -> List.map extract_qualid l, true
  | (VARG_STRING "inside") :: l -> List.map extract_qualid l, false
  | [] -> [], true
  | _ -> bad_vernac_args "inside/outside"

let _ = 
  add "SearchRewrite"
    (function
       | (VARG_CONSTR c) :: l ->
	   (fun () -> 
	      let _,pat = interp_constrpattern Evd.empty (Global.env()) c in
	      Search.search_rewrite pat (inside_outside l))
       | _ -> bad_vernac_args "SearchRewrite")

let _ = 
  add "SearchPattern"
    (function
       | (VARG_CONSTR c) :: l ->
	   (fun () -> 
	      let _,pat = interp_constrpattern Evd.empty (Global.env()) c in
	      Search.search_pattern  pat (inside_outside l))
       | _ -> bad_vernac_args "SearchPattern")

let _ =
  add "SEARCH"
    (function 
       | (VARG_QUALID qid) :: l ->
	   (fun () ->
	      let ref = locate_qualid dummy_loc qid in
	      Search.search_by_head ref (inside_outside l))
       | _ -> bad_vernac_args "SEARCH")

let _ =
  add "INSPECT"
    (function 
       | [VARG_NUMBER n] -> (fun () -> msg(inspect n))
       | _ -> bad_vernac_args "INSPECT")

let _ =
  add "SETUNDO"
    (function 
       | [VARG_NUMBER n] -> (fun () -> set_undo n)
       | _ -> bad_vernac_args "SETUNDO")

let _ =
  add "UNSETUNDO"
    (function 
       | [] -> (fun () -> reset_undo ())
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
           VARG_CONSTR c;
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
			 VARG_CONSTR arc;
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
			 VARG_CONSTR arc;
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
          VARG_CONSTR sort; 
          VARG_VARGLIST namec; 
          VARG_VARGLIST cfs] -> 
           let ps = join_binders binders in
           let cfs =
	     List.map
               (function 
		  | (VARG_VARGLIST 
                      [VARG_STRING str; VARG_STRING b; 
		       VARG_IDENTIFIER id; VARG_CONSTR c]) ->
		      let assum = match b with
			| "ASSUM" -> true
			| "DEF" -> false
			| _ -> bad_vernac_args "RECORD" in
		      (str = "COERCION", (id, assum, c))
		  | _ -> bad_vernac_args "RECORD")
               cfs in
           let const = match namec with 
             | [] -> add_prefix "Build_" struc
             | [VARG_IDENTIFIER id] -> id 
             | _ -> bad_vernac_args "RECORD" in
           let iscoe = (coe = "COERCION") in
	   let s = interp_sort sort in
	   fun () -> Record.definition_structure (iscoe,struc,ps,cfs,const,s)
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
			 VARG_CONSTR arf;
			 VARG_CONSTR ardef])
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
			VARG_CONSTR arf;
			VARG_CONSTR ardef])
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
			VARG_IDENTIFIER indid;
			VARG_CONSTR sort]) ->
		      let dep = match depstr with 
			| "DEP" -> true
                        | "NODEP" -> false
                        | _ -> anomaly "Unexpected string"
		      in 
		      (fid,dep,indid,sort)
		  | _ -> bad_vernac_args "INDUCTIONSCHEME") lmi
	   in 
	   fun () -> build_scheme lnamedepindsort
       | _ -> bad_vernac_args "INDUCTIONSCHEME")

let _ =
  add "SyntaxMacro"
    (function 
       | [VARG_IDENTIFIER id;VARG_CONSTR com] ->
	   (fun () -> syntax_definition id com)
       | [VARG_IDENTIFIER id;VARG_CONSTR com; VARG_NUMBER n] ->
           (fun () ->
              let rec aux t = function
                | 0 -> t
               	| n -> aux (ope("APPLIST",[t;ope("ISEVAR",[])])) (n-1)
              in 
	      syntax_definition id (aux com n))
       | _ -> bad_vernac_args "SyntaxMacro")

let _ =
  add "Require"
    (function 
       | [VARG_STRING import; VARG_STRING specif; VARG_QUALID qid] ->
	   fun () -> 
	     without_mes_ambig 
	       (Library.require_module 
      		  (if specif="UNSPECIFIED" then 
		     None 
		   else 
		     Some (specif="SPECIFICATION"))
		  qid None)
      	       (import="EXPORT") 
       | _ -> bad_vernac_args "Require")

let _ =
  add "RequireFrom"
    (function 
       | [VARG_STRING import; VARG_STRING specif;
      	  VARG_QUALID qid; VARG_STRING filename] ->
	   (fun () -> 
	      without_mes_ambig 
		(Library.require_module 
      		   (if specif="UNSPECIFIED" then 
		      None 
		    else 
		      Some (specif="SPECIFICATION"))
		   qid (Some filename))
		(import="EXPORT"))
       | _ -> bad_vernac_args "RequireFrom")

let _ =
  add "NOP"
    (function 
       | [] -> (fun () -> ())
       | _  -> bad_vernac_args "NOP")

let _ =
  add "CLASS"
    (function 
       | [VARG_STRING kind; VARG_QUALID qid] -> 
	   let stre = 
	     if kind = "LOCAL" then 
	       make_strength_0()
             else 
	       NeverDischarge 
	   in
	   fun () -> 
	     let ref = locate_qualid dummy_loc qid in
	     Class.try_add_new_class ref stre;
             if_verbose message
               ((Libnames.string_of_qualid qid) ^ " is now a class")
       | _ -> bad_vernac_args "CLASS")

let cl_of_qualid qid =
  match Libnames.repr_qualid qid with
    | [], id when string_of_id id = "FUNCLASS" -> Classops.CL_FUN
    | [], id when string_of_id id = "SORTCLASS" -> Classops.CL_SORT
    | _ -> Class.class_of_ref (locate_qualid dummy_loc qid)	

let _ =
  add "COERCION"
    (function 
       | [VARG_STRING kind;VARG_STRING identity;
          VARG_QUALID qid;VARG_QUALID qids;VARG_QUALID qidt] -> 
	   let stre = 
	     if (kind = "LOCAL") then 
	       make_strength_0()
             else 
	       NeverDischarge 
	   in
	   let isid = identity = "IDENTITY" in
	   let target = cl_of_qualid qidt in
	   let source = cl_of_qualid qids in
	   fun () ->
	     if isid then match Libnames.repr_qualid qid with
	       | [], id ->
		   Class.try_add_new_identity_coercion id stre source target
	       | _ -> bad_vernac_args "COERCION"
	     else
	       let ref = locate_qualid dummy_loc qid in
	       Class.try_add_new_coercion_with_target ref stre source target;
	       if_verbose
		 message
                 ((Libnames.string_of_qualid qid) ^ " is now a coercion")
       | _ -> bad_vernac_args "COERCION")

let _ =
  add "PrintGRAPH"
    (function 
       | [] -> (fun () -> ppnl (Prettyp.print_graph()))
       | _  -> bad_vernac_args "PrintGRAPH")

let _ =
  add "PrintCLASSES"
    (function 
       | [] -> (fun () -> ppnl (Prettyp.print_classes()))
       | _  -> bad_vernac_args "PrintCLASSES")

let _ =
  add "PrintCOERCIONS"
    (function 
       | [] -> (fun () -> ppnl (Prettyp.print_coercions()))
       | _  -> bad_vernac_args "PrintCOERCIONS")

let _ =
  add "PrintPATH"
    (function 
       | [VARG_IDENTIFIER ids;VARG_IDENTIFIER idt] -> 
	   (fun () -> ppnl (Prettyp.print_path_between ids idt))
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
       | [VARG_STRING univ; VARG_ASTLIST al] ->
           (fun () -> Metasyntax.add_grammar_obj univ al)
       | _ -> bad_vernac_args "GRAMMAR")

let _ =
  add "SYNTAX"
    (function
       | [VARG_STRING whatfor; VARG_ASTLIST sel] ->
           (fun () -> Metasyntax.add_syntax_obj whatfor sel)
       | _ -> bad_vernac_args "SYNTAX")
    
let _ =
  add "TACDEF"
    (let rec tacdef_fun lacc=function
        (VARG_IDENTIFIER name)::(VARG_AST tacexp)::tl ->
          tacdef_fun ((name,tacexp)::lacc) tl
       |[] ->
         fun () ->
           List.iter (fun (name,ve) -> Tacinterp.add_tacdef name ve) lacc
       |_ -> bad_vernac_args "TACDEF"
     in
     tacdef_fun [])

let _ =
  add "INFIX"
    (function
       | [VARG_AST assoc; VARG_NUMBER n; VARG_STRING inf; VARG_QUALID pref] ->
	   let ref = Termast.ast_of_qualid pref in
           (fun () ->
	      Metasyntax.add_infix (Extend.gram_assoc assoc) n inf ref)
       | _ -> bad_vernac_args "INFIX")

let _ =
  add "DISTFIX"
    (function
       | [VARG_AST assoc; VARG_NUMBER n; VARG_STRING s; VARG_QUALID pref] ->
	   let ref = Termast.ast_of_qualid pref in
           (fun () ->
              Metasyntax.add_distfix (Extend.gram_assoc assoc) n s ref)
       | _ -> bad_vernac_args "DISTFIX")

let _ =
  add "PrintGrammar"
    (function
       | [VARG_IDENTIFIER uni; VARG_IDENTIFIER ent] ->
           (fun () ->
              Metasyntax.print_grammar (string_of_id uni) (string_of_id ent))
       | _ -> bad_vernac_args "PrintGrammar")

(* Search commands *)

(***
let _ =
  add "Searchisos"
  (function
     | [VARG_CONSTR com] -> 
	 (fun () ->
	    let env = Global.env() in
	    let c = constr_of_com Evd.empty env com in
	    let cc = nf_betaiota env Evd.empty c in
            Searchisos.type_search cc)
     | _ -> bad_vernac_args "Searchisos")
***)

open Goptions

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
		SecondaryTable (string_of_id t,string_of_id f) in
	      match arg with
		| VARG_NUMBER n -> set_int_option_value key n
	 	| VARG_STRING s -> set_string_option_value key s
         	| _ -> error "No such type of option value")
       | [(VARG_IDENTIFIER t);(VARG_IDENTIFIER f)] -> 
	   (fun () ->
	      let key = 
		SecondaryTable (string_of_id t,string_of_id f) in
	      set_bool_option_value key true)
       | [(VARG_IDENTIFIER t);arg] -> 
	   (fun () ->
	      let key = PrimaryTable (string_of_id t) in
	      match arg with
		| VARG_NUMBER n -> set_int_option_value key n
	 	| VARG_STRING s -> set_string_option_value key s
         	| _ -> error "No such type of option value")
       | [(VARG_IDENTIFIER t)] -> 
	   (fun () ->
	      let key = PrimaryTable (string_of_id t) in
	      set_bool_option_value key true)
       | _ -> bad_vernac_args "VernacOption")

let _ =
  add "UnsetTableField"
    (function
       | [(VARG_IDENTIFIER t);(VARG_IDENTIFIER f)] -> 
	   (fun () ->
	      let key = 
		SecondaryTable (string_of_id t,string_of_id f) in
	      set_bool_option_value key false)
       | [(VARG_IDENTIFIER t)] -> 
	   (fun () ->
	      let key = PrimaryTable (string_of_id t) in
	      set_bool_option_value key false)
       | _ -> bad_vernac_args "VernacOption")

let _ =
  add "AddTableField"
    (function
       | [VARG_IDENTIFIER t; VARG_IDENTIFIER f; VARG_IDENTIFIER v] -> 
	   (fun () ->
	      let key = 
		SecondaryTable (string_of_id t,string_of_id f) in
	      try 
		(get_ident_table key)#add v
	      with Not_found -> 
		error_undeclared_key key)
       | [VARG_IDENTIFIER t; VARG_IDENTIFIER f; VARG_STRING s] -> 
	   (fun () ->
	      let key = 
		SecondaryTable (string_of_id t,string_of_id f) in
	      try 
		(get_string_table key)#add s
	      with Not_found -> 
		error_undeclared_key key)
       | [VARG_IDENTIFIER t; VARG_IDENTIFIER v] ->
	   (fun () ->
	      let key = PrimaryTable (string_of_id t) in
	      try 
		(get_ident_table key)#add v
	      with Not_found -> 
		error_undeclared_key key)
       | [VARG_IDENTIFIER t; VARG_STRING s] ->
	   (fun () ->
	      let key = PrimaryTable (string_of_id t) in
	      try 
		(get_string_table key)#add s
	      with Not_found -> 
		error_undeclared_key key)
       | _ -> bad_vernac_args "TableField")

let _ =
  add "RemoveTableField"
    (function
       | [VARG_IDENTIFIER t; VARG_IDENTIFIER f; VARG_IDENTIFIER v] -> 
	   (fun () ->
	      let key = 
		SecondaryTable (string_of_id t,string_of_id f) in
	      try 
		(get_ident_table key)#remove v
	      with Not_found -> 
		error_undeclared_key key)
       | [VARG_IDENTIFIER t; VARG_IDENTIFIER f; VARG_STRING v] -> 
	   (fun () ->
	      let key = 
		SecondaryTable (string_of_id t,string_of_id f) in
	      try 
		(get_string_table key)#remove v
	      with Not_found -> 
		error_undeclared_key key)
       | [VARG_IDENTIFIER t; VARG_IDENTIFIER v] -> 
	   (fun () ->
	      let key = PrimaryTable (string_of_id t) in
	      try 
		(get_ident_table key)#remove v
	      with Not_found -> 
		error_undeclared_key key)
       | [VARG_IDENTIFIER t; VARG_STRING v] -> 
	   (fun () ->
	      let key = PrimaryTable (string_of_id t) in
	      try 
		(get_string_table key)#remove v
	      with Not_found -> 
		error_undeclared_key key)
  |  _ -> bad_vernac_args "TableField")
    
let _ =
  add "MemTableField"
    (function
       | [VARG_IDENTIFIER t; VARG_IDENTIFIER f; VARG_IDENTIFIER v] -> 
	   (fun () ->
	      let key = 
		SecondaryTable (string_of_id t,string_of_id f) in
	      try 
		(get_ident_table key)#mem v
	      with Not_found -> 
		error_undeclared_key key)
       | [VARG_IDENTIFIER t; VARG_IDENTIFIER f; VARG_STRING v] -> 
	   (fun () ->
	      let key = 
		SecondaryTable (string_of_id t,string_of_id f) in
	      try 
		(get_string_table key)#mem v
	      with Not_found -> 
		error_undeclared_key key)
       | [VARG_IDENTIFIER t; VARG_IDENTIFIER v] -> 
	   (fun () ->
	      let key = PrimaryTable (string_of_id t) in
	      try 
		(get_ident_table key)#mem v
	      with Not_found -> 
		error_undeclared_key key)
       | [VARG_IDENTIFIER t; VARG_STRING v] -> 
	   (fun () ->
	      let key = PrimaryTable (string_of_id t) in
	      try 
		(get_string_table key)#mem v
	      with Not_found -> 
		error_undeclared_key key)
       |  _ -> bad_vernac_args "TableField")

let _ =
  add "PrintOption"
  (function
     | [VARG_IDENTIFIER t; VARG_IDENTIFIER f] -> 
	 (fun () ->
	    let key = SecondaryTable (string_of_id t,string_of_id f) in
	    try 
	      (get_ident_table key)#print
	    with not_found ->
	    try 
	      (get_string_table key)#print
	    with not_found ->
            try 
	      print_option_value key
            with Not_found -> 
	      error_undeclared_key key)
     | [VARG_IDENTIFIER t] -> 
	 (fun () ->
	    let key = PrimaryTable (string_of_id t) in
	    try 
	      (get_ident_table key)#print
	    with not_found ->
	    try 
	      (get_string_table key)#print
	    with not_found ->
            try 
	      print_option_value key
            with Not_found -> 
            if (string_of_id t) = "Tables" then 
	      print_tables ()
	    else 
	      msg(print_name (Libnames.make_qualid [] t)))
     | _ -> bad_vernac_args "TableField")


open Tactics
open Pfedit

(* 
   The first one is a command that should be a tactic. It has been
   added by Christine to patch an error in the design of the proof
   machine, and enables to instantiate existential variables when
   there are no more goals to solve. It cannot be a tactic since 
   all tactics fail if there are no further goals to prove. *)

let _ = 
  vinterp_add "EXISTENTIAL"
    (function 
       | [VARG_NUMBER n; VARG_CONSTR c] -> 
           (fun () -> instantiate_nth_evar_com n c)
       |  _  -> assert false)

(* The second is a stupid macro that should be replaced by ``Exact
   c. Save.'' all along the theories. *)

let _ = 
  vinterp_add "PROOF"
    (function 
       | [VARG_CONSTR c] ->
           (fun () -> (* by (tactic_com exact c) *)
              (* on experimente la synthese d'ise dans exact *)
              by (dyn_exact_check [Command c]); 
              save_named true)
       |   _  -> assert false)

let print_subgoals () = if_verbose show_open_subgoals_focused ()

let _ = 
  vinterp_add "SOLVE"
    (function l -> 
       let (n,tcom) = match l with 
	 | [VARG_NUMBER n;VARG_TACTIC tcom] -> (n,tcom)
	 |  _  -> invalid_arg "SOLVE"
       in
       (fun () -> 
	  if not (refining ()) then
	    error "Unknown command of the non proof-editing mode";
	  solve_nth n (Tacinterp.hide_interp tcom);
	  print_subgoals();
          (* in case a strict subtree was completed, 
             go back to the top of the prooftree *) 
	  if subtree_solved () then 
	    (reset_top_of_tree (); print_subgoals()) 
       ))

(* Coq syntax for ML commands *)

let _ = vinterp_add "DeclareMLModule"
	  (fun l ->
	     let sl = 
	       List.map 
		 (function 
		    | (VARG_STRING s) -> s 
		    | _ -> anomaly "DeclareMLModule : not a string") l
	     in
    	     fun () -> Mltop.declare_ml_modules sl)
	  
let _ = vinterp_add "AddMLPath"
	  (function 
	     | [VARG_STRING s] ->
		 (fun () -> Mltop.add_ml_dir (glob s))
	     | _ -> anomaly "AddMLPath : not a string")

let _ = vinterp_add "RecAddMLPath"
	  (function 
	     | [VARG_STRING s] ->
		 (fun () -> Mltop.add_rec_ml_dir (glob s))
	     | _ -> anomaly "RecAddMLPath : not a string")

let _ = vinterp_add "PrintMLPath"
	  (function 
	     | [] -> (fun () -> Mltop.print_ml_path ())
	     | _ -> anomaly "PrintMLPath : does not expect any argument")

let _ = vinterp_add "PrintMLModules"
	  (function 
	     | [] -> (fun () -> Mltop.print_ml_modules ())
	     | _ -> anomaly "PrintMLModules : does not expect an argument")

let _ = vinterp_add "DumpUniverses"
	  (function
	     | [] -> (fun () -> pp (Univ.pr_universes (Global.universes ())))
	     | [VARG_STRING s] ->
		 (fun () -> let output = open_out s in
		    try
		      Univ.dump_universes output (Global.universes ());
		      close_out output;
		      msg (**)( str ("Universes written to file \""^s^"\".") ++ fnl ()  )(**) 
		    with
			e -> close_out output; raise e
		 )
	     | _ -> 
		 anomaly "DumpUniverses : expects a filename or nothing as argument") 

(* Simulate the Intro(s) tactic *)

open Tactics

let id_of_name = function
    Anonymous -> id_of_string "H"
  | Name id   -> id;;

let rec do_renum avoid gl = function
    [] -> ""
  | [n] -> (string_of_id (fresh_id avoid (id_of_name n) gl))
  | n :: l -> let id = fresh_id avoid (id_of_name n) gl in
        (string_of_id id)^" "^(do_renum (id :: avoid) gl l)

let _ = vinterp_add "SHOWINTRO" 
	  (function 
	     | [] -> 
		 (fun () ->
		    let pf = get_pftreestate() in
		    let gl = nth_goal_of_pftreestate 1 pf in
		    let l,_= decompose_prod (strip_outer_cast (pf_concl gl)) in
		    let n = List.hd (List.rev_map fst l) in
		      message (string_of_id (fresh_id [] (id_of_name n) gl)))
	     | _ -> bad_vernac_args "Show Intro")

let _ =  vinterp_add "SHOWINTROS"
	   (function 
	      | [] -> 
		  (fun () ->
		     let pf = get_pftreestate() in
		     let gl = nth_goal_of_pftreestate 1 pf in
		     let l,_= decompose_prod (strip_outer_cast (pf_concl gl)) in
		     let l = List.rev_map fst l in
		       message (do_renum [] gl l))
	      | _ -> bad_vernac_args "Show Intros")
