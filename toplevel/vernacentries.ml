(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(* Concrete syntax of the mathematical vernacular MV V2.6 *)

open Pp
open Util
open Flags
open Names
open Entries
open Nameops
open Term
open Decl_mode
open Constrintern
open Prettyp
open Printer
open Tactic_printer
open Tacinterp
open Command
open Goptions
open Libnames
open Nametab
open Vernacexpr
open Decl_kinds
open Topconstr
open Pretyping
open Redexpr
open Syntax_def

(* arnaud: trucs factices *)
let get_pftreestate _ = Util.anomaly "Vernacentries.get_pftreestate: fantome"
let cursor_of_pftreestate _ = Util.anomaly "Vernacentries.cursor_of_pftreestate: fantome"
let evc_of_pftreestate _ = Util.anomaly "Vernacentries.evc_of_pftreestate: fantome"
let extract_open_pftreestate _ = Util.anomaly "Vernacentries.extract_open_pftreestate: fantome"
let proof_of_pftreestate _ = Util.anomaly "Vernacentries.proof_of_pftreestate: fantome"
let goal_of_proof _ = Util.anomaly "Vernacentries.goal_of_proof: fantome"
let top_goal_of_pftreestate _ = Util.anomaly "Vernacentries.top_goal_of_pftreestate: fantome"
let project _ = Util.anomaly "Vernacentries.project: fantome"
let nth_goal_of_pftreestate _ = Util.anomaly "Vernacentries.nth_goal_of_pftreestate: fantome"
let pf_concl _ = Util.anomaly "Vernacentries.pf_concl: fantome"
let refining () = true
let  top_of_tree _ = Util.anomaly "Vernacentries.top_of_tree: fantome"
let is_leaf_proof _ = Util.anomaly "Vernacentries.is_leaf_proof: fantome"
let by _ = Util.anomaly "Vernacentries.by: fantome"
let check_no_pending_proofs _ = Util.anomaly "Vernacentries.check_no_pending_proofs: fantome"
let solve_nth = Proof.db_run_tactic_on
let get_end_tac _ = Util.anomaly "Vernacentries.get_end_tac: fantome"
let subtree_solved  _ = Util.anomaly "Vernacentries.subtree_solved: fantome"
let make_focus _ = Util.anomaly "Vernacentries.make_focus: fantome"
let reset_top_of_script  _ = Util.anomaly "Vernacentries.reset_top_of_script: fantome"
let instantiate_nth_evar_com  _ = Util.anomaly "Vernacentries.instantiate_nth_evar_com: fantome"
let  set_end_tac _ = Util.anomaly "Vernacentries.set_end_tac: fantome"
let tree_solved _ = Util.anomaly "Vernacentries.tree_solved: fantome"
module Pfedit =
  struct
    let refining _ = Util.anomaly "Vernacentries.Pfedit.refining: fantome"
    let get_undo () = Some 18000
    let set_undo _ = Util.anomaly "Vernacentries.Pfedit.set_undo: fantome"
    let traverse _ = Util.anomaly "Vernacentries.traverse: fantome"
    let reset_top_of_tree _ = Util.anomaly "Vernacentries.reset_top_of_tree: fantome"
    let traverse_next_unproven _ = Util.anomaly "Vernacentries.traverse_next_unproven: fantome"
    let traverse_prev_unproven _ = Util.anomaly "Vernacentries.traverse_prev_unproven: fantome"
    let get_all_proof_names _ = Util.anomaly "Vernacentries.get_all_proof_names: fantome"
  end
let delete_all_proofs _ = Util.anomaly "Vernacentries.delete_all_proofs: fantome"
let get_goal_context _ = Util.anomaly "Vernacentries.get_goal_context: fantome"
let delete_current_proof _ = Util.anomaly "Vernacentries.delete_current_proof: fantome"
let delete_proof _ = Util.anomaly "Vernacentries.delete_proof: fantome"
let restart_proof _ = Util.anomaly "Vernacentries.restart_proof: fantome"
let suspend_proof _ = Util.anomaly "Vernacentries.suspend_proof: fantome"
let resume_last_proof _ = Util.anomaly "Vernacentries.resume_last_proof: fantome"
let resume_proof _ = Util.anomaly "Vernacentries.resume_proof: fantome"
let undo _ = Util.anomaly "Vernacentries.undo: fantome"
let undo_todepth _ = Util.anomaly "Vernacentries.undo_todepth: fantome"
let traverse_nth_goal _ = Util.anomaly "Vernacentries.traverse_nth_goal: fantome"
module Tacmach =
  struct
    let traverse _ = Util.anomaly "Vernacentries.Tacmach.traverse: fantome"
  end 

(* arnaud: /trucs factices *)

(* Pcoq hooks *)

type pcoq_hook = {
  start_proof : unit -> unit;
  solve : int -> unit;
  abort : string -> unit;
  search : searchable -> dir_path list * bool -> unit;
  print_name : reference -> unit;
  print_check : Environ.env -> Environ.unsafe_judgment -> unit;
  print_eval : Reductionops.reduction_function -> Environ.env -> Evd.evar_map -> constr_expr ->
    Environ.unsafe_judgment -> unit;
  show_goal : int option -> unit
}

let pcoq = ref None
let set_pcoq_hook f = pcoq := Some f

(* Misc *)

let cl_of_qualid = function
  | FunClass -> Classops.CL_FUN
  | SortClass -> Classops.CL_SORT
  | RefClass r -> Class.class_of_global (global_with_alias r)

(*******************)
(* "Show" commands *)

let show_proof () =
  let pts = get_pftreestate () in
  let cursor = cursor_of_pftreestate pts in
  let evc = evc_of_pftreestate pts in
  let (pfterm,meta_types) = extract_open_pftreestate pts in
  msgnl (str"LOC: " ++
    prlist_with_sep pr_spc pr_int (List.rev cursor) ++ fnl () ++
    str"Subgoals" ++ fnl () ++
    prlist (fun (mv,ty) -> Nameops.pr_meta mv ++ str" -> " ++ 
      pr_ltype ty ++ fnl ())
      meta_types
    ++ str"Proof: " ++ pr_lconstr (Evarutil.nf_evar evc pfterm))

let show_node () =
  Util.anomaly "Vernacentries.show_node: à restaurer" (* arnaud: à restaurer
  let pts = get_pftreestate () in
  let pf = proof_of_pftreestate pts
  and cursor = cursor_of_pftreestate pts in
  msgnl (prlist_with_sep pr_spc pr_int (List.rev cursor) ++ fnl () ++
         pr_goal (goal_of_proof pf) ++ fnl () ++
         (match pf.Proof_type.ref with
            | None -> (str"BY <rule>")
            | Some(r,spfl) ->
		(str"BY " ++ pr_rule r ++ fnl () ++
		 str"  " ++
		   hov 0 (prlist_with_sep pr_fnl pr_goal
			    (List.map goal_of_proof spfl)))))
		  *)
    
let show_script () =
  let pts = get_pftreestate () in
  let pf = proof_of_pftreestate pts
  and evc = evc_of_pftreestate pts in
  msgnl (print_treescript true evc pf)

let show_thesis () =
     msgnl (anomaly "TODO" )

let show_top_evars () =
  let pfts = get_pftreestate () in 
  let gls = top_goal_of_pftreestate pfts in 
  let sigma = project gls in 
  msg (pr_evars_int 1 (Evarutil.non_instantiated sigma))

let show_prooftree () =
  let pts = get_pftreestate () in
  let pf = proof_of_pftreestate pts
  and evc = evc_of_pftreestate pts in
  msg (print_proof evc (Global.named_context()) pf)

let print_subgoals () = if_verbose (fun () -> msg (pr_open_subgoals ())) ()

  (* Simulate the Intro(s) tactic *)

let show_intro all =
  let pf = get_pftreestate() in
  let gl = nth_goal_of_pftreestate 1 pf in
  let l,_= Sign.decompose_prod_assum (strip_outer_cast (pf_concl gl)) in
  if all 
  then 
    let lid = Tactics.find_intro_names l gl in 
    msgnl (hov 0 (prlist_with_sep  spc pr_id lid))
  else  
    try  
      let n = list_last l in
      msgnl (pr_id (List.hd (Tactics.find_intro_names [n] gl)))
    with Failure "list_last" -> message ""

let id_of_name = function 
  | Names.Anonymous -> id_of_string "x" 
  | Names.Name x -> x


(* Building of match expression *)
(* From ide/coq.ml *)
let make_cases s = 
  let qualified_name = Libnames.qualid_of_string s in
  let glob_ref = Nametab.locate qualified_name in
  match glob_ref with
    | Libnames.IndRef i -> 
	let {Declarations.mind_nparams = np}
	    , {Declarations.mind_consnames = carr ; Declarations.mind_nf_lc = tarr } 
	      = Global.lookup_inductive i in
	Util.array_fold_right2 
	  (fun n t l ->  
	     let (al,_) = Term.decompose_prod t in
	     let al,_ = Util.list_chop (List.length al - np) al in
	     let rec rename avoid = function 
	       | [] -> []
	       | (n,_)::l -> 
		   let n' = Termops.next_global_ident_away true (id_of_name n) avoid in
		   string_of_id n' :: rename (n'::avoid) l in
	     let al' = rename [] (List.rev al) in
	     (string_of_id n :: al') :: l)
	  carr tarr []
    | _ -> raise Not_found


let show_match id = 
  try
    let s = string_of_id (snd id) in
    let patterns = make_cases s in
    let cases = 
      List.fold_left 
	(fun acc x -> 
	  match x with
	    | [] -> assert false
	    | [x] -> "| "^ x  ^ " => \n" ^ acc
	    | x::l -> 
		"| (" ^ List.fold_left (fun acc s ->  acc ^ " " ^ s) x l ^ ")" 
		^ " => \n" ^ acc)
	"end" patterns in
    msg (str ("match # with\n" ^ cases))
  with Not_found -> error "Unknown inductive type"

(* "Print" commands *)

let print_path_entry (s,l) =
  (str s ++ str " " ++ tbrk (0,2) ++ str (string_of_dirpath l))

let print_loadpath () =
  let l = Library.get_full_load_paths () in
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
    let _,file = System.where_in_path (Library.get_load_paths ()) f in
    msgnl (str file)
  with Not_found -> 
    msgnl (hov 0 (str"Can't find file" ++ spc () ++ str f ++ spc () ++
		  str"on loadpath"))

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

let print_located_module r = 
  let (loc,qid) = qualid_of_reference r in
  let msg =
    try 
      let dir = Nametab.full_name_module qid in
      str "Module " ++ pr_dirpath dir
    with Not_found ->
      (if fst (repr_qualid qid) = empty_dirpath then
	str "No module is referred to by basename "
      else 
	str "No module is referred to by name ") ++ pr_qualid qid
  in msgnl msg  

(**********)
(* Syntax *)

let vernac_syntax_extension = Metasyntax.add_syntax_extension

let vernac_delimiters = Metasyntax.add_delimiters

let vernac_bind_scope sc cll = 
  List.iter (fun cl -> Metasyntax.add_class_scope sc (cl_of_qualid cl)) cll

let vernac_open_close_scope = Notation.open_close_scope

let vernac_arguments_scope local r scl =
  Notation.declare_arguments_scope local (global_with_alias r) scl

let vernac_infix = Metasyntax.add_infix

let vernac_notation = Metasyntax.add_notation

(***********)
(* Gallina *)

let start_proof_and_print idopt k t hook =
  start_proof_com idopt k t hook;
  print_subgoals ();
  if !pcoq <> None then (Option.get !pcoq).start_proof ()

let vernac_definition (local,_,_ as k) id def hook =
  match def with
  | ProveBody (bl,t) ->   (* local binders, typ *)
      if Lib.is_modtype () then
	errorlabstrm "Vernacentries.VernacDefinition"
	  (str "Proof editing mode not supported in module types")
      else
	let hook _ _ = () in
	start_proof_and_print (Some id) (local,DefinitionBody Definition) (bl,t) hook
  | DefineBody (bl,red_option,c,typ_opt) ->
      let red_option = match red_option with
        | None -> None
        | Some r -> 
	    let (evc,env)= Command.get_current_context () in
	    Some (interp_redexp env evc r) in
      declare_definition id k bl red_option c typ_opt hook

let vernac_start_proof kind sopt (bl,t) lettop hook =
  if not(refining ()) then
    if lettop then
      errorlabstrm "Vernacentries.StartProof"
	(str "Let declarations can only be used in proof editing mode");
  if Lib.is_modtype () then
    errorlabstrm "Vernacentries.StartProof"
      (str "Proof editing mode not supported in module types");
  start_proof_and_print sopt (Global, Proof kind) (bl,t) hook

let vernac_end_proof = function
  | Admitted -> admit ()
  | Proved (is_opaque,idopt) ->
    if not !Flags.print_emacs then if_verbose show_script ();
    match idopt with
    | None -> save_named is_opaque
    | Some ((_,id),None) -> save_anonymous is_opaque id
    | Some ((_,id),Some kind) -> save_anonymous_with_strength kind is_opaque id

  (* A stupid macro that should be replaced by ``Exact c. Save.'' all along
     the theories [??] *)

let vernac_exact_proof c =
  let pfs = top_of_tree (get_pftreestate()) in
  let pf = proof_of_pftreestate pfs in
    if (is_leaf_proof pf) then begin
      by (Tactics.exact_proof c);
      save_named true end
    else
      errorlabstrm "Vernacentries.ExactProof"
	(str "Command 'Proof ...' can only be used at the beginning of the proof")
  	
let vernac_assumption kind l nl=
  List.iter (fun (is_coe,(idl,c)) -> declare_assumption idl is_coe kind [] c nl) l

let vernac_inductive f indl = build_mutual indl f

let vernac_fixpoint = build_recursive

let vernac_cofixpoint = build_corecursive

let vernac_scheme = build_scheme

let vernac_combined_scheme = build_combined_scheme

(**********************)
(* Modules            *)

let vernac_import export refl =
  let import ref = Library.import_module export (qualid_of_reference ref) in
  List.iter import refl;
  Lib.add_frozen_state ()

let vernac_declare_module export id binders_ast mty_ast_o = 
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Lib.sections_are_opened () then
    error "Modules and Module Types are not allowed inside sections";
  let binders_ast = List.map
   (fun (export,idl,ty) ->
     if export <> None then
      error ("Arguments of a functor declaration cannot be exported. " ^
       "Remove the \"Export\" and \"Import\" keywords from every functor " ^
       "argument.")
     else (idl,ty)) binders_ast in
  Declaremods.declare_module 
    Modintern.interp_modtype Modintern.interp_modexpr
     id binders_ast (Some mty_ast_o) None;
  if_verbose message ("Module "^ string_of_id id ^" is declared");
  Option.iter (fun export -> vernac_import export [Ident (dummy_loc,id)]) export

let vernac_define_module export id binders_ast mty_ast_o mexpr_ast_o = 
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Lib.sections_are_opened () then
    error "Modules and Module Types are not allowed inside sections";
  match mexpr_ast_o with
    | None ->
       let binders_ast,argsexport =
        List.fold_right
         (fun (export,idl,ty) (args,argsexport) ->
           (idl,ty)::args, (List.map (fun (_,i) -> export,i)idl)@argsexport) binders_ast
             ([],[]) in
	Declaremods.start_module Modintern.interp_modtype export
	  id binders_ast mty_ast_o;
	if_verbose message 
	  ("Interactive Module "^ string_of_id id ^" started") ;
        List.iter
         (fun (export,id) ->
           Option.iter
            (fun export -> vernac_import export [Ident (dummy_loc,id)]) export
         ) argsexport
    | Some _ ->
       let binders_ast = List.map
        (fun (export,idl,ty) ->
          if export <> None then
           error ("Arguments of a functor definition can be imported only if" ^
                  " the definition is interactive. Remove the \"Export\" and " ^
                  "\"Import\" keywords from every functor argument.")
          else (idl,ty)) binders_ast in
	Declaremods.declare_module 
	  Modintern.interp_modtype Modintern.interp_modexpr
	  id binders_ast mty_ast_o mexpr_ast_o;
	if_verbose message 
	  ("Module "^ string_of_id id ^" is defined");
        Option.iter (fun export -> vernac_import export [Ident (dummy_loc,id)])
         export

let vernac_end_module export id =
  Declaremods.end_module id;
  if_verbose message ("Module "^ string_of_id id ^" is defined") ;
  Option.iter (fun export -> vernac_import export [Ident (dummy_loc,id)]) export


let vernac_declare_module_type id binders_ast mty_ast_o =
  if Lib.sections_are_opened () then
    error "Modules and Module Types are not allowed inside sections";
  
  match mty_ast_o with
    | None ->
       let binders_ast,argsexport =
        List.fold_right
         (fun (export,idl,ty) (args,argsexport) ->
           (idl,ty)::args, List.map (fun (_,i) -> export,i) idl) binders_ast
             ([],[]) in
	Declaremods.start_modtype Modintern.interp_modtype id binders_ast;
	if_verbose message 
	  ("Interactive Module Type "^ string_of_id id ^" started");
        List.iter
         (fun (export,id) ->
           Option.iter
            (fun export -> vernac_import export [Ident (dummy_loc,id)]) export
         ) argsexport
	  
    | Some base_mty ->
       let binders_ast = List.map
        (fun (export,idl,ty) ->
          if export <> None then
           error ("Arguments of a functor definition can be imported only if" ^
                  " the definition is interactive. Remove the \"Export\" " ^
                  "and \"Import\" keywords from every functor argument.")
          else (idl,ty)) binders_ast in
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
    | None -> add_prefix "Build_" (snd (snd struc))
    | Some (_,id) -> id in
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

let vernac_begin_section = Lib.open_section
let vernac_end_section = Lib.close_section

let vernac_end_segment id =
  check_no_pending_proofs ();
  let o = try Lib.what_is_opened () with 
      Not_found -> error "There is nothing to end." in
    match o with
      | _,Lib.OpenedModule (export,_,_) -> vernac_end_module export id
      | _,Lib.OpenedModtype _ -> vernac_end_modtype id
      | _,Lib.OpenedSection _ -> vernac_end_section id
      | _ -> anomaly "No more opened things"

let vernac_require import _ qidl =
  let qidl = List.map qualid_of_reference qidl in
  Library.require_library qidl import

let vernac_canonical r =
  Recordops.declare_canonical_structure (global_with_alias r)

let vernac_coercion stre ref qids qidt =
  let target = cl_of_qualid qidt in
  let source = cl_of_qualid qids in
  let ref' = global_with_alias ref in
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
  Decl_mode.check_not_proof_mode "Unknown proof instruction";
  begin
    if b then 
      solve_nth n (Tacinterp.hide_interp tcom (get_end_tac ()))
    else solve_nth n (Tacinterp.hide_interp tcom None)
  end;
  (* in case a strict subtree was completed, 
     go back to the top of the prooftree *) 
  if subtree_solved () then begin
    Flags.if_verbose msgnl (str "Subgoal proved");
    make_focus 0;
    reset_top_of_script ()
  end;
  print_subgoals();
  if !pcoq <> None then (Option.get !pcoq).solve n

  (* A command which should be a tactic. It has been
     added by Christine to patch an error in the design of the proof
     machine, and enables to instantiate existential variables when
     there are no more goals to solve. It cannot be a tactic since 
     all tactics fail if there are no further goals to prove. *)
  
let vernac_solve_existential = instantiate_nth_evar_com

let vernac_set_end_tac tac =
  if not (refining ()) then
    error "Unknown command of the non proof-editing mode";
  if tac <> (Tacexpr.TacId []) then set_end_tac (Tacinterp.interp tac) else ()
    (* TO DO verifier s'il faut pas mettre exist s | TacId s ici*)

(***********************)
(* Proof Language Mode *)

let vernac_decl_proof () = 
  check_not_proof_mode "Already in Proof Mode";
  if tree_solved () then 
    error "Nothing left to prove here."
  else
    begin
      Decl_proof_instr.go_to_proof_mode ();
      print_subgoals ()
    end

let vernac_return () = 
  match get_current_mode () with
      Mode_tactic ->
	Decl_proof_instr.return_from_tactic_mode ();
	print_subgoals ()
    | Mode_proof -> 
	error "\"return\" is only used after \"escape\"."
    | Mode_none -> 
	error "There is no proof to end." 

let vernac_proof_instr instr = 
  Decl_proof_instr.proof_instr instr;
  print_subgoals ()

(*****************************)
(* Auxiliary file management *)

let vernac_require_from export spec filename =
  Library.require_library_from_file None
    (System.expand_path_macros filename)
    export

let vernac_add_loadpath isrec pdir ldiropt =
  let pdir = System.expand_path_macros pdir in
  let alias = match ldiropt with
    | None -> Nameops.default_root_prefix
    | Some ldir -> ldir in
  (if isrec then Mltop.add_rec_path else Mltop.add_path) pdir alias

let vernac_remove_loadpath path =
  Library.remove_load_path (System.expand_path_macros path)

  (* Coq syntax for ML or system commands *)

let vernac_add_ml_path isrec path =
  (if isrec then Mltop.add_rec_ml_dir else Mltop.add_ml_dir)
    (System.expand_path_macros path)

let vernac_declare_ml_module l =
  Mltop.declare_ml_modules (List.map System.expand_path_macros l)

let vernac_chdir = function
  | None -> message (Sys.getcwd())
  | Some path ->
      begin
	try Sys.chdir (System.expand_path_macros path)
	with Sys_error str -> warning ("Cd failed: " ^ str)
      end;
      if_verbose message (Sys.getcwd())


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

let vernac_backto n = Lib.reset_label n

(* see also [vernac_backtrack] which combines undoing and resetting *)
(************)
(* Commands *)

let vernac_declare_tactic_definition = Tacinterp.add_tacdef

let vernac_hints = Auto.add_hints

let vernac_syntactic_definition = Command.syntax_definition 

let vernac_declare_implicits local r = function
  | Some imps ->
      Impargs.declare_manual_implicits local (global_with_alias r) imps
  | None -> 
      Impargs.declare_implicits local (global_with_alias r)

let vernac_reserve idl c =
  let t = Constrintern.interp_type Evd.empty (Global.env()) c in
  let t = Detyping.detype false [] [] t in
  List.iter (fun id -> Reserve.declare_reserved_type id t) idl

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
      optname  = "strict implicit arguments";
      optkey   = (SecondaryTable ("Strict","Implicit"));
      optread  = Impargs.is_strict_implicit_args;
      optwrite = Impargs.make_strict_implicit_args }

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "strong strict implicit arguments";
      optkey   = (TertiaryTable ("Strongly","Strict","Implicit"));
      optread  = Impargs.is_strongly_strict_implicit_args;
      optwrite = Impargs.make_strongly_strict_implicit_args }

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "contextual implicit arguments";
      optkey   = (SecondaryTable ("Contextual","Implicit"));
      optread  = Impargs.is_contextual_implicit_args;
      optwrite = Impargs.make_contextual_implicit_args }

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "implicit arguments defensive printing";
      optkey   = (TertiaryTable ("Reversible","Pattern","Implicit"));
      optread  = Impargs.is_reversible_pattern_implicit_args;
      optwrite = Impargs.make_reversible_pattern_implicit_args }

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "maximal insertion of implicit";
      optkey   = (TertiaryTable ("Maximal","Implicit","Insertion"));
      optread  = Impargs.is_maximal_implicit_args;
      optwrite = Impargs.make_maximal_implicit_args }

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "coercion printing";
      optkey   = (SecondaryTable ("Printing","Coercions"));
      optread  = (fun () -> !Constrextern.print_coercions);
      optwrite = (fun b ->  Constrextern.print_coercions := b) }

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "implicit arguments printing";
      optkey   = (SecondaryTable ("Printing","Implicit"));
      optread  = (fun () -> !Constrextern.print_implicits);
      optwrite = (fun b ->  Constrextern.print_implicits := b) }

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "implicit arguments defensive printing";
      optkey   = (TertiaryTable ("Printing","Implicit","Defensive"));
      optread  = (fun () -> !Constrextern.print_implicits_defensive);
      optwrite = (fun b ->  Constrextern.print_implicits_defensive := b) }

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "projection printing using dot notation";
      optkey   = (SecondaryTable ("Printing","Projections"));
      optread  = (fun () -> !Constrextern.print_projections);
      optwrite = (fun b ->  Constrextern.print_projections := b) }

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "notations printing";
      optkey   = (SecondaryTable ("Printing","Notations"));
      optread  = (fun () -> not !Constrextern.print_no_symbol);
      optwrite = (fun b ->  Constrextern.print_no_symbol := not b) }

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "raw printing";
      optkey   = (SecondaryTable ("Printing","All"));
      optread  = (fun () -> !Flags.raw_print);
      optwrite = (fun b -> Flags.raw_print := b) }

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "use of virtual machine inside the kernel";
      optkey   = (SecondaryTable ("Virtual","Machine"));
      optread  = (fun () -> Vconv.use_vm ());
      optwrite = (fun b -> Vconv.set_use_vm b) }

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "use of boxed definitions";
      optkey   = (SecondaryTable ("Boxed","Definitions"));
      optread  = Flags.boxed_definitions;
      optwrite = (fun b -> Flags.set_boxed_definitions b) } 

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "use of boxed values";
      optkey   = (SecondaryTable ("Boxed","Values"));
      optread  = (fun _ -> not (Vm.transp_values ()));
      optwrite = (fun b -> Vm.set_transp_values (not b)) } 

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
      optread=Flags.print_hyps_limit;
      optwrite=Flags.set_print_hyps_limit }

let _ =
  declare_int_option
    { optsync=true;
      optkey=SecondaryTable("Printing","Depth");
      optname="the printing depth";
      optread=Pp_control.get_depth_boxes;
      optwrite=Pp_control.set_depth_boxes }

let _ =
  declare_int_option
    { optsync=true;
      optkey=SecondaryTable("Printing","Width");
      optname="the printing width";
      optread=Pp_control.get_margin;
      optwrite=Pp_control.set_margin }

let _ =
  declare_bool_option
    { optsync=true;
      optkey=SecondaryTable("Printing","Universes");
      optname="the printing of universes";
      optread=(fun () -> !Constrextern.print_universes);
      optwrite=(fun b -> Constrextern.print_universes:=b) }

let vernac_debug b =
  set_debug (if b then Tactic_debug.DebugOn 0 else Tactic_debug.DebugOff)

let _ =
  declare_bool_option
    { optsync=false;
      optkey=SecondaryTable("Ltac","Debug");
      optname="Ltac debug";
      optread=(fun () -> get_debug () <> Tactic_debug.DebugOff);
      optwrite=vernac_debug }

let vernac_set_opacity opaq r =
  match global_with_alias r with
    | ConstRef sp ->
	if opaq then set_opaque_const sp
	else set_transparent_const sp
    | VarRef id ->
	if opaq then set_opaque_var id
	else set_transparent_var id
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
	if !pcoq <> None then (Option.get !pcoq).print_check env j
	else msg (print_judgment env j)
    | Some r ->
	let redfun = fst (reduction_of_red_expr (interp_redexp env evmap r)) in
	if !pcoq <> None
	then (Option.get !pcoq).print_eval redfun env evmap rc j
	else msg (print_eval redfun env evmap rc j)

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
  | PrintFullContext -> msg (print_full_context_typ ())
  | PrintSectionContext qid -> msg (print_sec_context_typ qid)
  | PrintInspect n -> msg (inspect n)
  | PrintGrammar ent -> Metasyntax.print_grammar ent
  | PrintLoadPath -> (* For compatibility ? *) print_loadpath ()
  | PrintModules -> msg (print_modules ())
  | PrintModule qid -> print_module qid
  | PrintModuleType qid -> print_modtype qid
  | PrintMLLoadPath -> Mltop.print_ml_path ()
  | PrintMLModules -> Mltop.print_ml_modules ()
  | PrintName qid -> 
      if !pcoq <> None then (Option.get !pcoq).print_name qid
      else msg (print_name qid)
  | PrintOpaqueName qid -> msg (print_opaque_name qid)
  | PrintGraph -> ppnl (Prettyp.print_graph())
  | PrintClasses -> ppnl (Prettyp.print_classes())
  | PrintLtac qid -> ppnl (Tacinterp.print_ltac (snd (qualid_of_reference qid)))
  | PrintCoercions -> ppnl (Prettyp.print_coercions())
  | PrintCoercionPaths (cls,clt) ->
      ppnl (Prettyp.print_path_between (cl_of_qualid cls) (cl_of_qualid clt))
  | PrintCanonicalConversions -> ppnl (Prettyp.print_canonical_projections ())
  | PrintUniverses None -> pp (Univ.pr_universes (Global.universes ()))
  | PrintUniverses (Some s) -> dump_universes s
  | PrintHint r -> Auto.print_hint_ref (global_with_alias r)
  | PrintHintGoal -> Auto.print_applicable_hint ()
  | PrintHintDbName s -> Auto.print_hint_db_by_name s
  | PrintRewriteHintDbName s -> Autorewrite.print_rewrite_hintdb s
  | PrintHintDb -> Auto.print_searchtable ()
  | PrintSetoids -> Setoid_replace.print_setoids()
  | PrintScopes ->
      pp (Notation.pr_scopes (Constrextern.without_symbols pr_lrawconstr))
  | PrintScope s ->
      pp (Notation.pr_scope (Constrextern.without_symbols pr_lrawconstr) s)
  | PrintVisibility s ->
      pp (Notation.pr_visibility (Constrextern.without_symbols pr_lrawconstr) s)
  | PrintAbout qid -> msgnl (print_about qid)
  | PrintImplicit qid -> msg (print_impargs qid)
(*spiwack: prints all the axioms and section variables used by a term *)
  | PrintAssumptions r ->
      let cstr = constr_of_global (global_with_alias r) in
      let nassumptions = Environ.assumptions cstr (Global.env ()) in
      msg 
      (try
        Printer.pr_assumptionset (Global.env ()) nassumptions
      with Not_found ->
        pr_reference r ++ str " is closed under the global context")

let global_module r =
  let (loc,qid) = qualid_of_reference r in
  try Nametab.full_name_module qid
  with Not_found -> 
    user_err_loc (loc, "global_module",
      str "Module/section " ++ pr_qualid qid ++ str " not found")

let interp_search_restriction = function
  | SearchOutside l -> (List.map global_module l, true)
  | SearchInside l -> (List.map global_module l, false)

open Search

let interp_search_about_item = function
  | SearchRef r -> GlobSearchRef (global_with_alias r)
  | SearchString s -> GlobSearchString s

let vernac_search s r =
  let r = interp_search_restriction r in
  if !pcoq <> None then (Option.get !pcoq).search s r else
  match s with
  | SearchPattern c ->
      let _,pat = interp_constrpattern Evd.empty (Global.env()) c in
      Search.search_pattern pat r
  | SearchRewrite c ->
      let _,pat = interp_constrpattern Evd.empty (Global.env()) c in
      Search.search_rewrite pat r
  | SearchHead ref ->
      Search.search_by_head (global_with_alias ref) r
  | SearchAbout sl ->
      Search.search_about (List.map interp_search_about_item sl) r

let vernac_locate = function
  | LocateTerm qid -> msgnl (print_located_qualid qid)
  | LocateLibrary qid -> print_located_library qid
  | LocateModule qid -> print_located_module qid
  | LocateFile f -> locate_file f
  | LocateNotation ntn ->
      ppnl (Notation.locate_notation (Constrextern.without_symbols pr_lrawconstr)
	(Metasyntax.standardize_locatable_notation ntn))

(********************)
(* Proof management *)

let vernac_goal = function
  | None -> ()
  | Some c ->
      if not (refining()) then begin
        let unnamed_kind = Lemma (* Arbitrary *) in
        start_proof_com None (Global, Proof unnamed_kind) c (fun _ _ ->());
	print_subgoals ()
      end else 
	error "repeated Goal not permitted in refining mode"

let vernac_abort = function
  | None ->
      delete_current_proof ();
      if_verbose message "Current goal aborted";
      if !pcoq <> None then (Option.get !pcoq).abort ""
  | Some id ->
      delete_proof id;
      let s = string_of_id (snd id) in
      if_verbose message ("Goal "^s^" aborted");
      if !pcoq <> None then (Option.get !pcoq).abort s

let vernac_abort_all () =
  if refining() then begin
    delete_all_proofs ();
    message "Current goals aborted"
  end else
    error "No proof-editing in progress"

let vernac_restart () = restart_proof(); print_subgoals ()

  (* Proof switching *)

let vernac_suspend = suspend_proof

let vernac_resume = function
  | None -> resume_last_proof ()
  | Some id -> resume_proof id

let vernac_undo n =
  undo n;
  print_subgoals ()

(* backtrack with [naborts] abort, then undo_todepth to [pnum], then
   back-to state number [snum]. This allows to backtrack proofs and
   state with one command (easier for proofgeneral). *)
let vernac_backtrack snum pnum naborts =
  for i = 1 to naborts do vernac_abort None done;
  undo_todepth pnum;
  vernac_backto snum;
  Pp.flush_all();
  (* there may be no proof in progress, even if no abort *)
  (try print_subgoals () with UserError _ -> ())
  

let vernac_focus gln =
  check_not_proof_mode "No focussing or Unfocussing in Proof Mode.";
  match gln with 
    | None -> traverse_nth_goal 1; print_subgoals ()
    | Some n -> traverse_nth_goal n; print_subgoals ()
	
  (* Reset the focus to the top of the tree *)
let vernac_unfocus () =
  check_not_proof_mode "No focussing or Unfocussing in Proof Mode.";
  make_focus 0; reset_top_of_script (); print_subgoals ()

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

let explain_proof occ =
  msg (apply_subproof (fun evd _ -> print_treescript true evd) occ)

let explain_tree occ =
  msg (apply_subproof print_proof occ)

let vernac_show = function
  | ShowGoal nopt ->
      if !pcoq <> None then (Option.get !pcoq).show_goal nopt
      else msg (match nopt with
	| None -> pr_open_subgoals ()
	| Some n -> pr_nth_open_subgoal n)
  | ShowGoalImplicitly None ->
      Constrextern.with_implicits msg (pr_open_subgoals ())
  | ShowGoalImplicitly (Some n) ->
      Constrextern.with_implicits msg (pr_nth_open_subgoal n)
  | ShowProof -> show_proof ()
  | ShowNode -> show_node ()
  | ShowScript -> show_script ()
  | ShowExistentials -> show_top_evars ()
  | ShowTree -> show_prooftree ()
  | ShowProofNames ->
      msgnl (prlist_with_sep pr_spc pr_id (Pfedit.get_all_proof_names()))
  | ShowIntros all -> show_intro all
  | ShowMatch id -> show_match id
  | ShowThesis -> show_thesis ()
  | ExplainProof occ -> explain_proof occ
  | ExplainTree occ -> explain_tree occ


let vernac_check_guard () =
  let pts = get_pftreestate () in
  let pf = proof_of_pftreestate pts in
  let (pfterm,_) = extract_open_pftreestate pts in
  let message = 
    try 
      Inductiveops.control_only_guard (Evd.evar_env (goal_of_proof pf))
	pfterm; 
      (str "The condition holds up to here")
    with UserError(_,s) -> 
      (str ("Condition violated : ") ++s)
  in 
  msgnl message

let interp c = match c with
  (* Control (done in vernac) *)
  | (VernacTime _ | VernacVar _ | VernacList _ | VernacLoad _) -> assert false

  (* Syntax *)
  | VernacTacticNotation (n,r,e) -> Metasyntax.add_tactic_notation (n,r,e)
  | VernacSyntaxExtension (lcl,sl) -> vernac_syntax_extension lcl sl
  | VernacDelimiters (sc,lr) -> vernac_delimiters sc lr
  | VernacBindScope (sc,rl) -> vernac_bind_scope sc rl
  | VernacOpenCloseScope sc -> vernac_open_close_scope sc
  | VernacArgumentsScope (lcl,qid,scl) -> vernac_arguments_scope lcl qid scl
  | VernacInfix (local,mv,qid,sc) -> vernac_infix local mv qid sc
  | VernacNotation (local,c,infpl,sc) -> vernac_notation local c infpl sc

  (* Gallina *)
  | VernacDefinition (k,(_,id),d,f) -> vernac_definition k id d f
  | VernacStartTheoremProof (k,(_,id),t,top,f) ->
      vernac_start_proof k (Some id) t top f
  | VernacEndProof e -> vernac_end_proof e
  | VernacExactProof c -> vernac_exact_proof c
  | VernacAssumption (stre,nl,l) -> vernac_assumption stre l nl
  | VernacInductive (finite,l) -> vernac_inductive finite l
  | VernacFixpoint (l,b) -> vernac_fixpoint l b
  | VernacCoFixpoint (l,b) -> vernac_cofixpoint l b
  | VernacScheme l -> vernac_scheme l
  | VernacCombinedScheme (id, l) -> vernac_combined_scheme id l

  (* Modules *)
  | VernacDeclareModule (export,(_,id),bl,mtyo) -> 
      vernac_declare_module export id bl mtyo
  | VernacDefineModule (export,(_,id),bl,mtyo,mexpro) -> 
      vernac_define_module export id bl mtyo mexpro
  | VernacDeclareModuleType ((_,id),bl,mtyo) -> 
      vernac_declare_module_type id bl mtyo

  (* Gallina extensions *)
  | VernacBeginSection (_,id) -> vernac_begin_section id

  | VernacEndSegment (_,id) -> vernac_end_segment id

  | VernacRecord (_,id,bl,s,idopt,fs) -> vernac_record id bl s idopt fs
  | VernacRequire (export,spec,qidl) -> vernac_require export spec qidl
  | VernacImport (export,qidl) -> vernac_import export qidl
  | VernacCanonical qid -> vernac_canonical qid
  | VernacCoercion (str,r,s,t) -> vernac_coercion str r s t
  | VernacIdentityCoercion (str,(_,id),s,t) -> vernac_identity_coercion str id s t

  (* Solving *)
  | VernacSolve (n,tac,b) -> vernac_solve n tac b
  | VernacSolveExistential (n,c) -> vernac_solve_existential n c

  (* MMode *)

  | VernacDeclProof -> vernac_decl_proof ()
  | VernacReturn -> vernac_return ()
  | VernacProofInstr stp -> vernac_proof_instr stp 

  (* /MMode *)

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
  | VernacBackTo n -> vernac_backto n

  (* Commands *)
  | VernacDeclareTacticDefinition (x,l) -> vernac_declare_tactic_definition x l
  | VernacHints (local,dbnames,hints) -> vernac_hints local dbnames hints
  | VernacSyntacticDefinition (id,c,l,b) ->vernac_syntactic_definition id c l b
  | VernacDeclareImplicits (local,qid,l) ->vernac_declare_implicits local qid l
  | VernacReserve (idl,c) -> vernac_reserve idl c
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
  | VernacBacktrack (snum,pnum,naborts) -> vernac_backtrack snum pnum naborts
  | VernacFocus n -> vernac_focus n
  | VernacUnfocus -> vernac_unfocus ()
  | VernacGo g -> vernac_go g
  | VernacShow s -> vernac_show s
  | VernacCheckGuard -> vernac_check_guard ()
  | VernacProof tac -> vernac_set_end_tac tac
  (* Toplevel control *)
  | VernacToplevelControl e -> raise e

  (* Extensions *)
  | VernacExtend (opn,args) -> Vernacinterp.call (opn,args)
