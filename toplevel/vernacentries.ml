(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(* Concrete syntax of the mathematical vernacular MV V2.6 *)

open Pp
open Util
open Options
open Names
open Entries
open Nameops
open Term
open Pfedit
open Tacmach
open Proof_trees
open Constrintern
open Prettyp
open Printer
open Tacinterp
open Command
open Goptions
open Libnames
open Nametab
open Vernacexpr
open Decl_kinds
open Topconstr
open Pretyping

(* Pcoq hooks *)

type pcoq_hook = {
  start_proof : unit -> unit;
  solve : int -> unit;
  abort : string -> unit;
  search : searchable -> dir_path list * bool -> unit;
  print_name : reference -> unit;
  print_check : Environ.unsafe_judgment -> unit;
  print_eval : (constr -> constr) -> Environ.env -> constr_expr -> 
    Environ.unsafe_judgment -> unit;
  show_goal : int option -> unit
}

let pcoq = ref None
let set_pcoq_hook f = pcoq := Some f

(*******************)
(* "Show" commands *)

  (* equivalent to pr_subgoals but start from the prooftree and 
    check for uninstantiated existential variables *)

let pr_subgoals_of_pfts pfts = 
  let gls = fst (Refiner.frontier (proof_of_pftreestate pfts)) in 
  let sigma = project (top_goal_of_pftreestate pfts) in
  pr_subgoals_existential sigma gls

let show_open_subgoals () =
  let pfts = get_pftreestate () in
  match focus() with
    | 0 -> 
	msg(pr_subgoals_of_pfts pfts)
    | n -> 
	let pf = proof_of_pftreestate pfts in
	let gls = fst(Refiner.frontier pf) in 
	if n > List.length gls then 
	  (make_focus 0; msg(pr_subgoals_of_pfts pfts))
	else if List.length gls < 2 then 
	  msg(pr_subgoal n gls)
	else 
	  msg (v 0 (int(List.length gls) ++ str" subgoals" ++ cut () ++ 
		      pr_subgoal n gls))

let show_nth_open_subgoal n =
  let pf = proof_of_pftreestate (get_pftreestate ()) in
  msg(pr_subgoal n (fst(Refiner.frontier pf)))

let show_proof () =
  let pts = get_pftreestate () in
  let pf = proof_of_pftreestate pts in
  let cursor = cursor_of_pftreestate pts in
  let evc = evc_of_pftreestate pts in
  let (pfterm,meta_types) = extract_open_pftreestate pts in
  msgnl (str"LOC: " ++
    prlist_with_sep pr_spc pr_int (List.rev cursor) ++ fnl () ++
    str"Subgoals" ++ fnl () ++
    prlist (fun (mv,ty) -> int mv ++ str" -> " ++ prtype ty ++ fnl ())
      meta_types
    ++ str"Proof: " ++ prterm (Evarutil.nf_evar evc pfterm))

let show_node () =
  let pts = get_pftreestate () in
  let pf = proof_of_pftreestate pts
  and cursor = cursor_of_pftreestate pts in
  msgnl (prlist_with_sep pr_spc pr_int (List.rev cursor) ++ fnl () ++
         prgl (goal_of_proof pf) ++ fnl () ++
         (match pf.Proof_type.ref with
            | None -> (str"BY <rule>")
            | Some(r,spfl) ->
		(str"BY " ++ Refiner.pr_rule r ++ fnl () ++
		 str"  " ++
		   hov 0 (prlist_with_sep pr_fnl prgl
			    (List.map goal_of_proof spfl)))))
    
let show_script () =
  let pts = get_pftreestate () in
  let pf = proof_of_pftreestate pts
  and evc = evc_of_pftreestate pts in
  msgnl (Refiner.print_script true evc (Global.named_context()) pf)

let show_top_evars () =
  let pfts = get_pftreestate () in 
  let gls = top_goal_of_pftreestate pfts in 
  let sigma = project gls in 
  msg (pr_evars_int 1 (Evd.non_instantiated sigma))

let show_prooftree () =
  let pts = get_pftreestate () in
  let pf = proof_of_pftreestate pts
  and evc = evc_of_pftreestate pts in
  msg (Refiner.print_proof evc (Global.named_context()) pf)

let print_subgoals () = if_verbose show_open_subgoals ()

  (* Simulate the Intro(s) tactic *)

let fresh_id_of_name avoid gl = function
    Anonymous -> Tactics.fresh_id avoid (id_of_string "H") gl
  | Name id   -> id

let rec do_renum avoid gl = function
    [] -> mt ()
  | [n] -> pr_id (fresh_id_of_name avoid gl n)
  | n :: l ->
      let id = fresh_id_of_name avoid gl n in
      pr_id id ++ spc () ++ do_renum (id :: avoid) gl l

let show_intro all =
  let pf = get_pftreestate() in
  let gl = nth_goal_of_pftreestate 1 pf in
  let l,_= decompose_prod (strip_outer_cast (pf_concl gl)) in
  let nl = List.rev_map fst l in
  if all then
    msgnl (do_renum [] gl nl)
  else
    try 
      let n = List.hd nl in
      msgnl (pr_id (fresh_id_of_name [] gl n))
    with Failure "hd" -> message "" 

(********************)
(* "Print" commands *)

let print_path_entry (s,l) =
  (str s ++ tbrk (0,2) ++ str (string_of_dirpath l))

let print_loadpath () =
  let l = Library.get_full_load_path () in
  msgnl (Pp.t (str "Physical path:                                 " ++
		 tab () ++ str "Logical Path:" ++ fnl () ++ 
		 prlist_with_sep pr_fnl print_path_entry l))

let print_modules () =
  let opened = Library.opened_libraries ()
  and loaded = Library.loaded_libraries () in
  let loaded_opened = list_intersect loaded opened
  and only_loaded = list_subtract loaded opened in
  str"Loaded and imported library files: " ++ 
  pr_vertical_list pr_dirpath loaded_opened ++ fnl () ++
  str"Loaded and not imported library files: " ++
  pr_vertical_list pr_dirpath only_loaded


let print_module r =
  let (loc,qid) = qualid_of_reference r in
  try
    let globdir = Nametab.locate_dir qid in
      match globdir with
	  DirModule (dirpath,(mp,_)) ->
	    msgnl (Printmod.print_module (Printmod.printable_body dirpath) mp)
	| _ -> raise Not_found
  with
      Not_found -> msgnl (str"Unknown Module " ++ pr_qualid qid)

let print_modtype r = 
  let (loc,qid) = qualid_of_reference r in
  try
    let kn = Nametab.locate_modtype qid in
      msgnl (Printmod.print_modtype kn)
  with
      Not_found -> msgnl (str"Unknown Module Type " ++ pr_qualid qid)

let dump_universes s =
  let output = open_out s in
  try
    Univ.dump_universes output (Global.universes ());
    close_out output;
    msgnl (str ("Universes written to file \""^s^"\".")) 
  with
      e -> close_out output; raise e


(*********************)
(* "Locate" commands *)

let locate_file f =
  try
    let _,file =
      System.where_in_path (Library.get_load_path()) f in
    msgnl (str file)
  with Not_found -> 
    msgnl (hov 0 (str"Can't find file" ++ spc () ++ str f ++ spc () ++
		  str"on loadpath"))

let print_located_qualid r =
  let (loc,qid) = qualid_of_reference r in
  let msg = 
    try
      let ref = Nametab.locate qid in
      let ref_str = match ref with
	  ConstRef _ -> "Constant"
	| IndRef _ -> "Inductive"
	| ConstructRef _ -> "Constructor"
	| VarRef _ -> "Variable"
      in
      let sp = Nametab.sp_of_global None ref in
	str ref_str ++ spc () ++ pr_sp sp
    with Not_found -> 
      try
	let kn = Nametab.locate_syntactic_definition qid in
	let sp = Nametab.sp_of_syntactic_definition kn in
	  str "Syntactic Definition" ++ spc () ++ pr_sp sp
      with Not_found ->
	try
	  let s,dir = match Nametab.locate_dir qid with
	    | DirOpenModule (dir,_) -> "Open Module", dir
	    | DirOpenModtype (dir,_) -> "Open Module Type", dir
	    | DirOpenSection (dir,_) -> "Open Section", dir
	    | DirModule (dir,_) -> "Module", dir
	    | DirClosedSection dir -> "Closed Section", dir
	  in
	    str s ++ spc () ++ pr_dirpath dir
	with Not_found ->
	  try
	    let sp = Nametab.full_name_modtype qid in
	      str "Module Type" ++ spc () ++ pr_sp sp
	  with Not_found ->
	    pr_qualid qid ++ str " is not a defined object"
  in
    msgnl (hov 0 msg)

(*let print_path_entry (s,l) =
  (str s ++ tbrk (0,2) ++ str (string_of_dirpath l))

let print_loadpath () =
  let l = Library.get_full_load_path () in
  msgnl (Pp.t (str "Physical path:                                 " ++
		 tab () ++ str "Logical Path:" ++ fnl () ++ 
		 prlist_with_sep pr_fnl print_path_entry l))
*)

let msg_found_library = function
  | Library.LibLoaded, fulldir, file ->
      msgnl(pr_dirpath fulldir ++ str " has been loaded from file" ++ fnl () ++
      str file)
  | Library.LibInPath, fulldir, file ->
      msgnl(pr_dirpath fulldir ++ str " is bound to file " ++ str file)
let msg_notfound_library loc qid = function
  | Library.LibUnmappedDir ->
      let dir = fst (repr_qualid qid) in
      user_err_loc (loc,"locate_library",
        str "Cannot find a physical path bound to logical path " ++
           pr_dirpath dir ++ fnl ())
  | Library.LibNotFound ->
      msgnl (hov 0 
	(str"Unable to locate library" ++ spc () ++ pr_qualid qid))
  | e -> assert false

let print_located_library r =
  let (loc,qid) = qualid_of_reference r in
  try msg_found_library (Library.locate_qualified_library qid)
  with e -> msg_notfound_library loc qid e


(**********)
(* Syntax *)

let vernac_syntax = Metasyntax.add_syntax_obj

let vernac_grammar = Metasyntax.add_grammar_obj

let vernac_syntax_extension = Metasyntax.add_syntax_extension

let vernac_delimiters = Metasyntax.add_delimiters

let vernac_open_scope = Symbols.open_scope

let vernac_arguments_scope qid scl =
  Symbols.declare_arguments_scope (global qid) scl

let vernac_infix = Metasyntax.add_infix

let vernac_distfix = Metasyntax.add_distfix

let vernac_notation = Metasyntax.add_notation

(***********)
(* Gallina *)

let start_proof_and_print idopt k t hook =
  start_proof_com idopt k t hook;
  print_subgoals ();
  if !pcoq <> None then (out_some !pcoq).start_proof ()

let vernac_definition local id def hook =
  match def with
  | ProveBody (bl,t) ->   (* local binders, typ *)
      if Lib.is_modtype () then
	errorlabstrm "Vernacentries.VernacDefinition"
	  (str "Proof editing mode not supported in module types")
      else
	let hook _ _ = () in
        let kind = if local=Local then IsLocal else IsGlobal DefinitionBody in
	  start_proof_and_print (Some id) kind (bl,t) hook
  | DefineBody (bl,red_option,c,typ_opt) ->
      let red_option = match red_option with
        | None -> None
        | Some r -> 
	    let (evc,env)= Command.get_current_context () in
	    Some (interp_redexp env evc r) in
      let ref = declare_definition id local bl red_option c typ_opt in
      hook local ref

let vernac_start_proof kind sopt (bl,t) lettop hook =
  if not(refining ()) then
    if lettop then
      errorlabstrm "Vernacentries.StartProof"
	(str "Let declarations can only be used in proof editing mode");
  if Lib.is_modtype () then
    errorlabstrm "Vernacentries.StartProof"
      (str "Proof editing mode not supported in module types");
  start_proof_and_print sopt (IsGlobal (Proof kind)) (bl,t) hook

let vernac_end_proof is_opaque idopt =
  if_verbose show_script ();
  match idopt with
    | None -> save_named is_opaque
    | Some (id,None) -> save_anonymous is_opaque id
    | Some (id,Some kind) -> save_anonymous_with_strength kind is_opaque id

  (* A stupid macro that should be replaced by ``Exact c. Save.'' all along
     the theories [??] *)

let vernac_exact_proof c =
  by (Tactics.exact_proof c); 
  save_named true

let vernac_assumption (islocal,_ as kind) l =
  List.iter
    (fun (is_coe,(id,c)) ->
      let r = declare_assumption id kind [] c in
      if is_coe then Class.try_add_new_coercion r islocal) l

let vernac_inductive f indl = build_mutual indl f

let vernac_fixpoint = build_recursive

let vernac_cofixpoint = build_corecursive

let vernac_scheme = build_scheme

let vernac_rule = build_rule

(**********************)
(* Modules            *)

let vernac_declare_module id binders_ast mty_ast_o mexpr_ast_o = 
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Lib.sections_are_opened () then
    error "Modules and Module Types are not allowed inside sections";

  if not (Lib.is_modtype ()) then
    error "Declare Module allowed in module types only";

  let constrain_mty = match mty_ast_o with
      Some (_,true) -> true
    | _ -> false
  in

  match mty_ast_o, constrain_mty, mexpr_ast_o with
    | _, false, None ->  (* no ident, no/soft type *)
	Declaremods.start_module Modintern.interp_modtype
	  id binders_ast mty_ast_o;
	if_verbose message 
	  ("Interactive Declaration of Module "^ string_of_id id ^" started")
	  
    | Some _, true, None           (* no ident, hard type *)
    | _, false, Some (CMEident _) ->  (* ident, no/soft type *)
	Declaremods.declare_module 
	  Modintern.interp_modtype Modintern.interp_modexpr
	  id binders_ast mty_ast_o mexpr_ast_o;
	if_verbose message 
	  ("Module "^ string_of_id id ^" is declared")

    | _, true, Some (CMEident _) -> (* ident, hard type *)
	error "You cannot declare an equality and a type in module declaration"

    | _, _, Some _ ->    (* not ident *)
	error "Only simple modules allowed in module declarations"

    | None,true,None -> assert false  (* 1st None ==> false *)

let vernac_define_module id binders_ast mty_ast_o mexpr_ast_o = 
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Lib.sections_are_opened () then
    error "Modules and Module Types are not allowed inside sections";
 
  if Lib.is_modtype () then
    error "Module definitions not allowed in module types. Use Declare Module instead";

  match mexpr_ast_o with
    | None ->
	Declaremods.start_module Modintern.interp_modtype
	  id binders_ast mty_ast_o;
	if_verbose message 
	  ("Interactive Module "^ string_of_id id ^" started")
	  
    | Some _ ->
	Declaremods.declare_module 
	  Modintern.interp_modtype Modintern.interp_modexpr
	  id binders_ast mty_ast_o mexpr_ast_o;
	if_verbose message 
	  ("Module "^ string_of_id id ^" is defined")

(* let vernac_declare_module id binders_ast mty_ast_o mexpr_ast_o =  *)
(*   (\* We check the state of the system (in section, in module type) *)
(*      and what module information is supplied *\) *)
(*   if Lib.sections_are_opened () then *)
(*     error "Modules and Module Types are not allowed inside sections"; *)
 
(*   let constrain_mty = match mty_ast_o with *)
(*       Some (_,true) -> true *)
(*     | _ -> false *)
(*   in *)

(*   match Lib.is_modtype (), mty_ast_o, constrain_mty, mexpr_ast_o with *)
(*     | _, None, _, None  *)
(*     | true, Some _, false, None *)
(*     | false, _, _, None -> *)
(* 	Declaremods.start_module Modintern.interp_modtype *)
(* 	  id binders_ast mty_ast_o; *)
(* 	if_verbose message  *)
(* 	  ("Interactive Module "^ string_of_id id ^" started") *)
	  
(*     | true, Some _, true, None *)
(*     | true, _, false, Some (CMEident _) *)
(*     | false, _, _, Some _ -> *)
(* 	Declaremods.declare_module  *)
(* 	  Modintern.interp_modtype Modintern.interp_modexpr *)
(* 	  id binders_ast mty_ast_o mexpr_ast_o; *)
(* 	if_verbose message  *)
(* 	  ("Module "^ string_of_id id ^" is defined") *)

(*     | true, _, _, _ -> *)
(* 	error "Module definition not allowed in a Module Type" *)


let vernac_end_module id =
  Declaremods.end_module id;
  if_verbose message 
    (if Lib.is_modtype () then 
       "Module "^ string_of_id id ^" is declared"
     else
       "Module "^ string_of_id id ^" is defined")

  


let vernac_declare_module_type id binders_ast mty_ast_o =
  if Lib.sections_are_opened () then
    error "Modules and Module Types are not allowed inside sections";
  
  match mty_ast_o with
    | None ->
	Declaremods.start_modtype Modintern.interp_modtype id binders_ast;
	if_verbose message 
	  ("Interactive Module Type "^ string_of_id id ^" started")
	  
    | Some base_mty ->
	Declaremods.declare_modtype Modintern.interp_modtype 
	  id binders_ast base_mty;
	if_verbose message 
	  ("Module Type "^ string_of_id id ^" is defined")


let vernac_end_modtype id =
  Declaremods.end_modtype id;
  if_verbose message 
    ("Module Type "^ string_of_id id ^" is defined")


(**********************)
(* Gallina extensions *)

let vernac_record struc binders sort nameopt cfs =
  let const = match nameopt with 
    | None -> add_prefix "Build_" (snd struc)
    | Some id -> id in
  let sigma = Evd.empty in
  let env = Global.env() in
  let s = interp_constr sigma env sort in
  let s = Reductionops.whd_betadeltaiota env sigma s in
  let s = match kind_of_term s with
    | Sort s -> s
    | _ -> user_err_loc
        (constr_loc sort,"definition_structure", str "Sort expected") in
  Record.definition_structure (struc,binders,cfs,const,s)

  (* Sections *)

let vernac_begin_section id = let _ = Lib.open_section id in ()

let vernac_end_section id =
  Discharge.close_section (is_verbose ()) id


let vernac_end_segment id =
  check_no_pending_proofs ();
  try
    match Lib.what_is_opened () with
      | _,Lib.OpenedModule _ -> vernac_end_module id
      | _,Lib.OpenedModtype _ -> vernac_end_modtype id
      | _,Lib.OpenedSection _ -> vernac_end_section id
      | _ -> anomaly "No more opened things"
  with
      Not_found -> error "There is nothing to end."

let is_obsolete_module (_,qid) =
  match repr_qualid qid with
  | dir, id when dir = empty_dirpath ->
      (match string_of_id id with
	| ("Refine" | "Inv" | "Equality" | "EAuto" | "AutoRewrite"
	  | "EqDecide" | "Xml" |  "Extraction" | "Tauto" | "Setoid_replace"
          | "Elimdep" )
	  -> true
	| _ -> false)
  | _ -> false

let vernac_require import _ qidl =
  let qidl = List.map qualid_of_reference qidl in
  try
    match import with
      | None -> List.iter Library.read_library qidl
      | Some b -> Library.require_library None qidl b
  with e ->
  (* Compatibility message *)
    let qidl' = List.filter is_obsolete_module qidl in
    if qidl' = qidl then
      List.iter
	(fun (_,qid) ->
	  warning ("Module "^(string_of_qualid qid)^
	  " is now built-in and shouldn't be required")) qidl
    else
      raise e
      
let vernac_import export qidl =
  let qidl = List.map qualid_of_reference qidl in
  if export then
    List.iter Library.export_library qidl
  else
    let import (loc,qid) = 
      try
	let mp = Nametab.locate_module qid in
	  Declaremods.import_module mp
      with Not_found ->
	user_err_loc
        (loc,"vernac_import",
	 str ((string_of_qualid qid)^" is not a module"))
    in
      List.iter import qidl;
      Lib.add_frozen_state ()

let vernac_canonical locqid =
  Recordobj.objdef_declare (Nametab.global locqid)

let cl_of_qualid = function
  | FunClass -> Classops.CL_FUN
  | SortClass -> Classops.CL_SORT
  | RefClass r -> Class.class_of_ref (Nametab.global r)

let vernac_coercion stre ref qids qidt =
  let target = cl_of_qualid qidt in
  let source = cl_of_qualid qids in
  let ref' = Nametab.global ref in
  Class.try_add_new_coercion_with_target ref' stre source target;
  if_verbose message ((string_of_reference ref) ^ " is now a coercion")

let vernac_identity_coercion stre id qids qidt =
  let target = cl_of_qualid qidt in
  let source = cl_of_qualid qids in
  Class.try_add_new_identity_coercion id stre source target


(***********)
(* Solving *)
let vernac_solve n tcom b =
  if not (refining ()) then
    error "Unknown command of the non proof-editing mode";
  begin
    if b then 
      solve_nth n (Tacinterp.hide_interp tcom (get_end_tac ()))
    else solve_nth n (Tacinterp.hide_interp tcom None)
  end;
  print_subgoals();
  (* in case a strict subtree was completed, 
     go back to the top of the prooftree *) 
  if subtree_solved () then 
    (reset_top_of_tree (); print_subgoals());
  if !pcoq <> None then (out_some !pcoq).solve n

  (* A command which should be a tactic. It has been
     added by Christine to patch an error in the design of the proof
     machine, and enables to instantiate existential variables when
     there are no more goals to solve. It cannot be a tactic since 
     all tactics fail if there are no further goals to prove. *)
  
let vernac_solve_existential = instantiate_nth_evar_com

let vernac_set_end_tac tac =
  if not (refining ()) then
    error "Unknown command of the non proof-editing mode";
  set_end_tac (Tacinterp.interp tac)

 
   
(*****************************)
(* Auxiliary file management *)

let vernac_require_from export spec filename =
  Library.require_library_from_file spec None filename export

let vernac_add_loadpath isrec pdir ldiropt =
  let alias = match ldiropt with
    | None -> Nameops.default_root_prefix
    | Some ldir -> ldir in
  (if isrec then Mltop.add_rec_path else Mltop.add_path) pdir alias

let vernac_remove_loadpath = Library.remove_path

  (* Coq syntax for ML or system commands *)

let vernac_add_ml_path isrec s =
  (if isrec then Mltop.add_rec_ml_dir else Mltop.add_ml_dir) (System.glob s)

let vernac_declare_ml_module l = Mltop.declare_ml_modules l

let vernac_chdir = function
  | None -> print_endline (Sys.getcwd())
  | Some s ->
      begin
	try Sys.chdir (System.glob s)
	with Sys_error str -> warning ("Cd failed: " ^ str)
      end;
      if_verbose print_endline (Sys.getcwd())


(********************)
(* State management *)

let abort_refine f x =
  if Pfedit.refining() then delete_all_proofs ();
  f x
  (* used to be: error "Must save or abort current goal first" *)

let vernac_write_state file = abort_refine States.extern_state file

let vernac_restore_state file = abort_refine States.intern_state file


(*************)
(* Resetting *)

let vernac_reset_name id = abort_refine Lib.reset_name id

let vernac_reset_initial () = abort_refine Lib.reset_initial ()

let vernac_back n = Lib.back n


(************)
(* Commands *)

let vernac_declare_tactic_definition = Tacinterp.add_tacdef

let vernac_hints = Auto.add_hints

let vernac_syntactic_definition id c = function
  | None -> syntax_definition id c
  | Some n ->
      let l = list_tabulate (fun _ -> (CHole (dummy_loc),None)) n in
      let c = CApp (dummy_loc,c,l) in
      syntax_definition id c

let vernac_declare_implicits locqid = function
  | Some imps -> Impargs.declare_manual_implicits (Nametab.global locqid) imps
  | None -> Impargs.declare_implicits (Nametab.global locqid)

let make_silent_if_not_pcoq b =
  if !pcoq <> None then 
    error "Turning on/off silent flag is not supported in Centaur mode"
  else make_silent b

let _ =
  declare_bool_option 
    { optsync  = false;
      optname  = "silent";
      optkey   = (PrimaryTable "Silent");
      optread  = is_silent;
      optwrite = make_silent_if_not_pcoq }

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "implicit arguments";
      optkey   = (SecondaryTable ("Implicit","Arguments"));
      optread  = Impargs.is_implicit_args;
      optwrite = Impargs.make_implicit_args }

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "strict implicits";
      optkey   = (SecondaryTable ("Strict","Implicits"));
      optread  = (fun () -> !Impargs.strict_implicit_args);
      optwrite = (fun b ->  Impargs.strict_implicit_args := b) }

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "contextual implicits";
      optkey   = (SecondaryTable ("Contextual","Implicits"));
      optread  = (fun () -> !Impargs.contextual_implicit_args);
      optwrite = (fun b ->  Impargs.contextual_implicit_args := b) }

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "coercion printing";
      optkey   = (SecondaryTable ("Printing","Coercions"));
      optread  = (fun () -> !Termast.print_coercions);
      optwrite = (fun b ->  Termast.print_coercions := b) }

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "symbols printing";
      optkey   = (SecondaryTable ("Printing","Symbols"));
      optread  = (fun () -> not !Constrextern.print_no_symbol);
      optwrite = (fun b ->  Constrextern.print_no_symbol := not b) }

let _ =
  declare_int_option
    { optsync=false;
      optkey=PrimaryTable("Undo");
      optname="the undo limit";
      optread=Pfedit.get_undo;
      optwrite=Pfedit.set_undo }

let _ =
  declare_int_option
    { optsync=false;
      optkey=SecondaryTable("Hyps","Limit");
      optname="the hypotheses limit";
      optread=Options.print_hyps_limit;
      optwrite=Options.set_print_hyps_limit }

let _ =
  declare_int_option
    { optsync=true;
      optkey=SecondaryTable("Printing","Depth");
      optname="the printing depth";
      optread=Pp_control.get_depth_boxes;
      optwrite=Pp_control.set_depth_boxes }

let vernac_set_opacity opaq locqid =
  match Nametab.global locqid with
    | ConstRef sp ->
	if opaq then Tacred.set_opaque_const sp
	else Tacred.set_transparent_const sp
    | VarRef id ->
	if opaq then Tacred.set_opaque_var id
	else Tacred.set_transparent_var id
    | _ -> error "cannot set an inductive type or a constructor as transparent"

let vernac_set_option key = function
  | StringValue s -> set_string_option_value key s
  | IntValue n -> set_int_option_value key (Some n)
  | BoolValue b -> set_bool_option_value key b

let vernac_unset_option key =
  try set_bool_option_value key false
  with _ ->
  set_int_option_value key None

let vernac_add_option key lv =
  let f = function
    | StringRefValue s -> (get_string_table key)#add s
    | QualidRefValue locqid -> (get_ref_table key)#add locqid
  in
  try List.iter f lv with Not_found -> error_undeclared_key key

let vernac_remove_option key lv =
  let f = function
  | StringRefValue s -> (get_string_table key)#remove s
  | QualidRefValue locqid -> (get_ref_table key)#remove locqid
  in
  try List.iter f lv with Not_found -> error_undeclared_key key

let vernac_mem_option key lv =
  let f = function
  | StringRefValue s -> (get_string_table key)#mem s
  | QualidRefValue locqid -> (get_ref_table key)#mem locqid
  in
  try List.iter f lv with Not_found -> error_undeclared_key key

let vernac_print_option key =
  try (get_ref_table key)#print
  with Not_found ->
  try (get_string_table key)#print
  with Not_found ->
  try print_option_value key
  with Not_found -> error_undeclared_key key

let get_current_context_of_args = function
  | Some n -> get_goal_context n
  | None -> get_current_context ()

let vernac_check_may_eval redexp glopt rc =
  let (evmap,env) = get_current_context_of_args glopt in
  let c = interp_constr evmap env rc in
  let j = Typeops.typing env c in
  match redexp with
    | None ->
	if !pcoq <> None then (out_some !pcoq).print_check j
	else msg (print_judgment env j)
    | Some r ->
	let redfun = Tacred.reduction_of_redexp (interp_redexp env evmap r) in
	if !pcoq <> None
	then (out_some !pcoq).print_eval (redfun env evmap) env rc j
	else msg (print_eval redfun env j)

  (* The same but avoiding the current goal context if any *)
let vernac_global_check c =
  let evmap = Evd.empty in
  let env = Global.env() in
  let c = interp_constr evmap env c in
  let senv = Global.safe_env() in
  let j = Safe_typing.typing senv c in
  msg (print_safe_judgment env j)

let vernac_print = function
  | PrintTables -> print_tables ()
  | PrintLocalContext -> msg (print_local_context ())
  | PrintFullContext -> msg (print_full_context_typ ())
  | PrintSectionContext qid -> msg (print_sec_context_typ qid)
  | PrintInspect n -> msg (inspect n)
  | PrintGrammar (uni,ent) -> Metasyntax.print_grammar uni ent
  | PrintLoadPath -> (* For compatibility ? *) print_loadpath ()
  | PrintModules -> msg (print_modules ())
  | PrintModule qid -> print_module qid
  | PrintModuleType qid -> print_modtype qid
  | PrintMLLoadPath -> Mltop.print_ml_path ()
  | PrintMLModules -> Mltop.print_ml_modules ()
  | PrintName qid -> 
      if !pcoq <> None then (out_some !pcoq).print_name qid
      else msg (print_name qid)
  | PrintOpaqueName qid -> msg (print_opaque_name qid)
  | PrintGraph -> ppnl (Prettyp.print_graph())
  | PrintClasses -> ppnl (Prettyp.print_classes())
  | PrintCoercions -> ppnl (Prettyp.print_coercions())
  | PrintCoercionPaths (cls,clt) ->
      ppnl (Prettyp.print_path_between (cl_of_qualid cls) (cl_of_qualid clt))
  | PrintUniverses None -> pp (Univ.pr_universes (Global.universes ()))
  | PrintUniverses (Some s) -> dump_universes s
  | PrintHint qid -> Auto.print_hint_ref (Nametab.global qid)
  | PrintHintGoal -> Auto.print_applicable_hint ()
  | PrintHintDbName s -> Auto.print_hint_db_by_name s
  | PrintHintDb -> Auto.print_searchtable ()
  | PrintScope s -> pp (Symbols.pr_scope (Constrextern.without_symbols pr_rawterm) s)

let global_module r =
  let (loc,qid) = qualid_of_reference r in
  try Nametab.full_name_module qid
  with Not_found -> 
    user_err_loc (loc, "global_module",
      str "Module/section " ++ pr_qualid qid ++ str " not found")

let interp_search_restriction = function
  | SearchOutside l -> (List.map global_module l, true)
  | SearchInside l -> (List.map global_module l, false)

let vernac_search s r =
  let r = interp_search_restriction r in
  if !pcoq <> None then (out_some !pcoq).search s r else
  match s with
  | SearchPattern c ->
      let _,pat = interp_constrpattern Evd.empty (Global.env()) c in
      Search.search_pattern pat r
  | SearchRewrite c ->
      let _,pat = interp_constrpattern Evd.empty (Global.env()) c in
      Search.search_rewrite pat r
  | SearchHead locqid ->
      Search.search_by_head (Nametab.global locqid) r
  | SearchAbout locqid ->
      Search.search_about (Nametab.global locqid) r

let vernac_locate = function
  | LocateTerm qid -> print_located_qualid qid
  | LocateLibrary qid -> print_located_library qid
  | LocateFile f -> locate_file f
  | LocateNotation ntn ->
      ppnl (Symbols.locate_notation (Constrextern.without_symbols pr_rawterm) ntn)

(********************)
(* Proof management *)

let vernac_goal = function
  | None -> ()
  | Some c ->
      if not (refining()) then begin
        let unnamed_kind = Lemma (* Arbitrary *) in
        start_proof_com None (IsGlobal (Proof unnamed_kind)) c (fun _ _ ->());
	print_subgoals ()
      end else 
	error "repeated Goal not permitted in refining mode"

let vernac_abort = function
  | None ->
      delete_current_proof ();
      if_verbose message "Current goal aborted";
      if !pcoq <> None then (out_some !pcoq).abort ""
  | Some id ->
      delete_proof id;
      let s = string_of_id (snd id) in
      if_verbose message ("Goal "^s^" aborted");
      if !pcoq <> None then (out_some !pcoq).abort s

let vernac_abort_all () =
  if refining() then begin
    delete_all_proofs ();
    message "Current goals aborted"
  end else
    error "No proof-editing in progress"

let vernac_restart () = restart_proof(); show_open_subgoals ()

  (* Proof switching *)

let vernac_suspend = suspend_proof

let vernac_resume = function
  | None -> resume_last_proof ()
  | Some id -> resume_proof id

let vernac_undo n =
  undo n;
  show_open_subgoals ()

  (* Est-ce normal que "Focus" ne semble pas se comporter comme "Focus 1" ? *)
let vernac_focus = function
  | None -> make_focus 1; show_open_subgoals ()
  | Some n -> traverse_nth_goal n; show_open_subgoals ()

  (* Reset the focus to the top of the tree *)
let vernac_unfocus () =
  make_focus 0; reset_top_of_tree (); show_open_subgoals ()

let vernac_go = function
  | GoTo n -> Pfedit.traverse n;show_node()
  | GoTop -> Pfedit.reset_top_of_tree ();show_node()
  | GoNext -> Pfedit.traverse_next_unproven ();show_node()
  | GoPrev -> Pfedit.traverse_prev_unproven ();show_node()

let apply_subproof f occ =
  let pts = get_pftreestate() in
  let evc = evc_of_pftreestate pts in
  let rec aux pts = function
    | [] -> pts
    | (n::l) -> aux (Tacmach.traverse n pts) occ in 
  let pts = aux pts (occ@[-1]) in
  let pf = proof_of_pftreestate pts in
  f evc (Global.named_context()) pf

let explain_proof occ = msg (apply_subproof (Refiner.print_script true) occ)

let explain_tree occ = msg (apply_subproof Refiner.print_proof occ)

let vernac_show = function
  | ShowGoal nopt ->
      if !pcoq <> None then (out_some !pcoq).show_goal nopt
      else (match nopt with
	| None -> show_open_subgoals ()
	| (Some n) -> show_nth_open_subgoal n)
  | ShowGoalImplicitly None -> Impargs.implicitly show_open_subgoals ()
  | ShowGoalImplicitly (Some n) -> Impargs.implicitly show_nth_open_subgoal n
  | ShowProof -> show_proof ()
  | ShowNode -> show_node ()
  | ShowScript -> show_script ()
  | ShowExistentials -> show_top_evars ()
  | ShowTree -> show_prooftree ()
  | ShowProofNames ->
      msgnl (prlist_with_sep pr_spc pr_id (Pfedit.get_all_proof_names()))
  | ShowIntros all -> show_intro all
  | ExplainProof occ -> explain_proof occ
  | ExplainTree occ -> explain_tree occ

let vernac_check_guard () =
  let pts = get_pftreestate () in
  let pf = proof_of_pftreestate pts 
  and cursor = cursor_of_pftreestate pts in
  let (pfterm,_) = extract_open_pftreestate pts in
  let message = 
    try 
      Inductiveops.control_only_guard (Evarutil.evar_env (goal_of_proof pf))
	pfterm; 
      (str "The condition holds up to here")
    with UserError(_,s) -> 
      (str ("Condition violated : ") ++s)
  in 
  msgnl message

let vernac_debug b =
  set_debug (if b then Tactic_debug.DebugOn else Tactic_debug.DebugOff)


(**************************)
(* Not supported commands *)
(***
let _ =
  add "ResetSection"
    (function 
       | [VARG_IDENTIFIER id] ->
	   (fun () -> reset_section (string_of_id id))
       | _ -> bad_vernac_args "ResetSection")

(* Modules *)

let _ =
  vinterp_add "BeginModule"
    (function 
       | [VARG_IDENTIFIER id] ->
	   let s = string_of_id id in
	   let lpe,_ = System.find_file_in_path (Library.get_load_path ()) (s^".v") in
	   let dir = extend_dirpath (Library.find_logical_path lpe) id in
	   fun () ->
	     Lib.start_module dir
       | _ -> bad_vernac_args "BeginModule")

let _ =
  vinterp_add "WriteModule"
    (function 
       | [VARG_IDENTIFIER id] ->
	   let mid = Lib.end_module id in
	   fun () -> let m = string_of_id id in Library.save_module_to mid m
       | [VARG_IDENTIFIER id; VARG_STRING f] ->
	   let mid = Lib.end_module id in
	   fun () -> Library.save_module_to mid f
       | _ -> bad_vernac_args "WriteModule")

let _ =
  vinterp_add "CLASS"
    (function 
       | [VARG_STRING kind; VARG_QUALID qid] -> 
	   let stre = 
	     if kind = "LOCAL" then 
	       make_strength_0()
             else 
	       Nametab.NeverDischarge 
	   in
	   fun () -> 
	     let ref = Nametab.global (dummy_loc, qid) in
	     Class.try_add_new_class ref stre;
             if_verbose message
               ((string_of_qualid qid) ^ " is now a class")
       | _ -> bad_vernac_args "CLASS")

(* Meta-syntax commands *)
let _ =
  add "TOKEN"
    (function
       | [VARG_STRING s] -> (fun () -> Metasyntax.add_token_obj s)
       | _ -> bad_vernac_args "TOKEN")
***)

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

let interp c = match c with
  (* Control (done in vernac) *)
  | (VernacTime _ | VernacVar _ | VernacList _ | VernacLoad _) -> assert false
  | (VernacV7only _ | VernacV8only _) -> assert false

  (* Syntax *)
  | VernacSyntax (whatfor,sel) -> vernac_syntax whatfor sel
  | VernacTacticGrammar al -> Metasyntax.add_tactic_grammar al
  | VernacGrammar (univ,al) -> vernac_grammar univ al
  | VernacSyntaxExtension (s,l) -> vernac_syntax_extension s l
  | VernacDelimiters (sc,lr) -> vernac_delimiters sc lr
  | VernacOpenScope sc -> vernac_open_scope sc
  | VernacArgumentsScope (qid,scl) -> vernac_arguments_scope qid scl
  | VernacInfix (assoc,n,inf,qid,b,sc) -> vernac_infix assoc n inf qid b sc
  | VernacDistfix (assoc,n,inf,qid,sc) -> vernac_distfix assoc n inf qid sc
  | VernacNotation (inf,c,pl,sc) -> vernac_notation inf c pl sc

  (* Gallina *)
  | VernacDefinition (k,id,d,f,_) -> vernac_definition k id d f
  | VernacStartTheoremProof (k,id,t,top,f) ->
      vernac_start_proof k (Some id) t top f
  | VernacEndProof (opaq,idopt) -> vernac_end_proof opaq idopt
  | VernacExactProof c -> vernac_exact_proof c
  | VernacAssumption (stre,l) -> vernac_assumption stre l
  | VernacInductive (finite,l) -> vernac_inductive finite l
  | VernacFixpoint l -> vernac_fixpoint l
  | VernacCoFixpoint l -> vernac_cofixpoint l
  | VernacScheme l -> vernac_scheme l
  | VernacRule (ctx,l,r) -> vernac_rule ctx (l,r)

  (* Modules *)
  | VernacDeclareModule (id,bl,mtyo,mexpro) -> 
      vernac_declare_module id bl mtyo mexpro
  | VernacDefineModule (id,bl,mtyo,mexpro) -> 
      vernac_define_module id bl mtyo mexpro
  | VernacDeclareModuleType (id,bl,mtyo) -> 
      vernac_declare_module_type id bl mtyo

  (* Gallina extensions *)
  | VernacBeginSection id -> vernac_begin_section id

  | VernacEndSegment id -> vernac_end_segment id

  | VernacRecord (id,bl,s,idopt,fs) -> vernac_record id bl s idopt fs
  | VernacRequire (export,spec,qidl) -> vernac_require export spec qidl
  | VernacImport (export,qidl) -> vernac_import export qidl
  | VernacCanonical qid -> vernac_canonical qid
  | VernacCoercion (str,r,s,t) -> vernac_coercion str r s t
  | VernacIdentityCoercion (str,id,s,t) -> vernac_identity_coercion str id s t

  (* Solving *)
  | VernacSolve (n,tac,b) -> vernac_solve n tac b
  | VernacSolveExistential (n,c) -> vernac_solve_existential n c

  (* Auxiliary file and library management *)
  | VernacRequireFrom (exp,spec,f) -> vernac_require_from exp spec f
  | VernacAddLoadPath (isrec,s,alias) -> vernac_add_loadpath isrec s alias
  | VernacRemoveLoadPath s -> vernac_remove_loadpath s
  | VernacAddMLPath (isrec,s) -> vernac_add_ml_path isrec s
  | VernacDeclareMLModule l -> vernac_declare_ml_module l
  | VernacChdir s -> vernac_chdir s

  (* State management *)
  | VernacWriteState s -> vernac_write_state s
  | VernacRestoreState s -> vernac_restore_state s

  (* Resetting *)
  | VernacResetName id -> vernac_reset_name id
  | VernacResetInitial -> vernac_reset_initial ()
  | VernacBack n -> vernac_back n

  (* Commands *)
  | VernacDeclareTacticDefinition (x,l) -> vernac_declare_tactic_definition x l
  | VernacHints (dbnames,hints) -> vernac_hints dbnames hints
  | VernacHintDestruct (id,l,p,n,tac) -> Dhyp.add_destructor_hint id l p n tac
  | VernacSyntacticDefinition (id,c,n) -> vernac_syntactic_definition id c n
  | VernacDeclareImplicits (qid,l) -> vernac_declare_implicits qid l
  | VernacSetOpacity (opaq, qidl) -> List.iter (vernac_set_opacity opaq) qidl
  | VernacSetOption (key,v) -> vernac_set_option key v
  | VernacUnsetOption key -> vernac_unset_option key
  | VernacRemoveOption (key,v) -> vernac_remove_option key v
  | VernacAddOption (key,v) -> vernac_add_option key v
  | VernacMemOption (key,v) -> vernac_mem_option key v
  | VernacPrintOption key -> vernac_print_option key
  | VernacCheckMayEval (r,g,c) -> vernac_check_may_eval r g c
  | VernacGlobalCheck c -> vernac_global_check c
  | VernacPrint p -> vernac_print p
  | VernacSearch (s,r) -> vernac_search s r
  | VernacLocate l -> vernac_locate l
  | VernacComments l -> if_verbose message ("Comments ok\n")
  | VernacNop -> ()

  (* Proof management *)
  | VernacGoal t -> vernac_start_proof Theorem None ([],t) false (fun _ _ ->())
  | VernacAbort id -> vernac_abort id
  | VernacAbortAll -> vernac_abort_all ()
  | VernacRestart -> vernac_restart ()
  | VernacSuspend -> vernac_suspend ()
  | VernacResume id -> vernac_resume id
  | VernacUndo n -> vernac_undo n
  | VernacFocus n -> vernac_focus n
  | VernacUnfocus -> vernac_unfocus ()
  | VernacGo g -> vernac_go g
  | VernacShow s -> vernac_show s
  | VernacCheckGuard -> vernac_check_guard ()
  | VernacDebug b -> vernac_debug b
  | VernacProof tac -> vernac_set_end_tac tac
  (* Toplevel control *)
  | VernacToplevelControl e -> raise e

  (* Extensions *)
  | VernacExtend (opn,args) -> Vernacinterp.call (opn,args)
