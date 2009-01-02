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
open Pfedit
open Tacmach
open Proof_trees
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
    
let show_script () =
  let pts = get_pftreestate () in
  let pf = proof_of_pftreestate pts
  and evc = evc_of_pftreestate pts in
  msgnl_with !Pp_control.deep_ft (print_treescript evc pf)

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
  with Not_found -> error "Unknown inductive type."

(* "Print" commands *)

let print_path_entry (s,l) =
  (str (string_of_dirpath l) ++ str " " ++ tbrk (0,0) ++ str s)

let print_loadpath () =
  let l = Library.get_full_load_paths () in
  msgnl (Pp.t (str "Logical Path:                 " ++
		 tab () ++ str "Physical path:" ++ fnl () ++
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
    let _,file = System.where_in_path false (Library.get_load_paths ()) f in
    msgnl (str file)
  with Not_found -> 
    msgnl (hov 0 (str"Can't find file" ++ spc () ++ str f ++ spc () ++
		  str"on loadpath"))

let msg_found_library = function
  | Library.LibLoaded, fulldir, file ->
      msgnl (hov 0
	(pr_dirpath fulldir ++ strbrk " has been loaded from file " ++
	 str file))
  | Library.LibInPath, fulldir, file ->
      msgnl (hov 0
	(pr_dirpath fulldir ++ strbrk " is bound to file " ++ str file))
let msg_notfound_library loc qid = function
  | Library.LibUnmappedDir ->
      let dir = fst (repr_qualid qid) in
      user_err_loc (loc,"locate_library",
        strbrk "Cannot find a physical path bound to logical path " ++
           pr_dirpath dir ++ str".")
  | Library.LibNotFound ->
      msgnl (hov 0 
	(strbrk "Unable to locate library " ++ pr_qualid qid ++ str"."))
  | e -> assert false

let print_located_library r =
  let (loc,qid) = qualid_of_reference r in
  try msg_found_library (Library.locate_qualified_library false qid)
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

let global_with_alias r =
  let gr = global_with_alias r in
    Dumpglob.add_glob (loc_of_reference r) gr;
    gr

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

let start_proof_and_print k l hook =
  start_proof_com k l hook;
  print_subgoals ();
  if !pcoq <> None then (Option.get !pcoq).start_proof ()

let vernac_definition (local,_,_ as k) (loc,id as lid) def hook =
  Dumpglob.dump_definition lid false "def";
  (match def with
    | ProveBody (bl,t) ->   (* local binders, typ *)
 	if Lib.is_modtype () then
 	  errorlabstrm "Vernacentries.VernacDefinition"
 	    (str "Proof editing mode not supported in module types")
 	else
 	  let hook _ _ = () in
 	    start_proof_and_print (local,DefinitionBody Definition) 
	      [Some lid, (bl,t)] hook
    | DefineBody (bl,red_option,c,typ_opt) ->
 	let red_option = match red_option with
          | None -> None
          | Some r -> 
 	      let (evc,env)= Command.get_current_context () in
 		Some (interp_redexp env evc r) in
 	  declare_definition id k bl red_option c typ_opt hook)
 	      
let vernac_start_proof kind l lettop hook =
  if Dumpglob.dump () then
    List.iter (fun (id, _) -> 
      match id with
	| Some lid -> Dumpglob.dump_definition lid false "prf"
	| None -> ()) l;
  if not(refining ()) then
    if lettop then
      errorlabstrm "Vernacentries.StartProof"
	(str "Let declarations can only be used in proof editing mode.");
  if Lib.is_modtype () then
    errorlabstrm "Vernacentries.StartProof"
      (str "Proof editing mode not supported in module types.");
  start_proof_and_print (Global, Proof kind) l hook

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
	(strbrk "Command 'Proof ...' can only be used at the beginning of the proof.")
  	
let vernac_assumption kind l nl=
  let global = fst kind = Global in
    List.iter (fun (is_coe,(idl,c)) -> 
      if Dumpglob.dump () then
	List.iter (fun lid -> 
	  if global then Dumpglob.dump_definition lid false "ax" 
	  else Dumpglob.dump_definition lid true "var") idl;
      declare_assumption idl is_coe kind [] c false false nl) l

let vernac_record k finite struc binders sort nameopt cfs =
  let const = match nameopt with 
    | None -> add_prefix "Build_" (snd (snd struc))
    | Some (_,id as lid) ->
	Dumpglob.dump_definition lid false "constr"; id in
  let sigma = Evd.empty in
  let env = Global.env() in
  let s = Option.map (fun x ->
    let s = Reductionops.whd_betadeltaiota env sigma (interp_constr sigma env x) in
      match kind_of_term s with
      | Sort s -> s
      | _ -> user_err_loc
          (constr_loc x,"definition_structure", str "Sort expected.")) sort
  in
    if Dumpglob.dump () then (
      Dumpglob.dump_definition (snd struc) false "rec";
      List.iter (fun ((_, x), _) ->
	match x with
	| Vernacexpr.AssumExpr ((loc, Name id), _) -> Dumpglob.dump_definition (loc,id) false "proj"
	| _ -> ()) cfs);
    ignore(Record.definition_structure (k,finite,struc,binders,cfs,const,s))
      
let vernac_inductive finite indl = 
  if Dumpglob.dump () then
    List.iter (fun (((coe,lid), _, _, _, cstrs), _) ->
      match cstrs with 
      | Constructors cstrs ->
	  Dumpglob.dump_definition lid false"ind";
	  List.iter (fun (_, (lid, _)) ->
	    Dumpglob.dump_definition lid false "constr") cstrs
      | _ -> () (* dumping is done by vernac_record (called below) *) )
    indl;
  match indl with
  | [ ( id , bl , c , Some b, RecordDecl (oc,fs) ), None ] -> 
      vernac_record (match b with Class true -> Class false | _ -> b)
	finite id bl c oc fs
  | [ ( id , bl , c , Some (Class true), Constructors [l]), _ ] -> 
      let f = 
	let (coe, ((loc, id), ce)) = l in
	  ((coe, AssumExpr ((loc, Name id), ce)), None)
      in vernac_record (Class true) finite id bl c None [f]
  | [ ( id , bl , c , Some (Class true), _), _ ] -> 
      Util.error "Definitional classes must have a single method"
  | [ ( id , bl , c , Some (Class false), Constructors _), _ ] ->
      Util.error "Inductive classes not supported"
  | [ ( _ , _ , _ , _, RecordDecl _ ) , _ ] -> 
      Util.error "where clause not supported for (co)inductive records"
  | _ -> let unpack = function 
      | ( (_, id) , bl , c , _ , Constructors l ) , ntn  -> ( id , bl , c , l ) , ntn
      | _ -> Util.error "Cannot handle mutually (co)inductive records."
    in
    let indl = List.map unpack indl in
      Command.build_mutual indl finite

let vernac_fixpoint l b = 
  if Dumpglob.dump () then
    List.iter (fun ((lid, _, _, _, _), _) -> Dumpglob.dump_definition lid false "def") l;
  build_recursive l b

let vernac_cofixpoint l b =
  if Dumpglob.dump () then
    List.iter (fun ((lid, _, _, _), _) -> Dumpglob.dump_definition lid false "def") l;
  build_corecursive l b

let vernac_scheme = build_scheme

let vernac_combined_scheme = build_combined_scheme

(**********************)
(* Modules            *)

let vernac_import export refl =
  let import ref = 
    Library.import_module export (qualid_of_reference ref)
  in
    List.iter import refl;
    Lib.add_frozen_state ()

let vernac_declare_module export (loc, id) binders_ast mty_ast_o = 
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Lib.sections_are_opened () then
    error "Modules and Module Types are not allowed inside sections.";
  let binders_ast = List.map
   (fun (export,idl,ty) ->
     if export <> None then
      error ("Arguments of a functor declaration cannot be exported. " ^
       "Remove the \"Export\" and \"Import\" keywords from every functor " ^
       "argument.")
     else (idl,ty)) binders_ast in
  let mp = Declaremods.declare_module 
    Modintern.interp_modtype Modintern.interp_modexpr
    id binders_ast (Some mty_ast_o) None
  in 
    Dumpglob.dump_moddef loc mp "mod";
    if_verbose message ("Module "^ string_of_id id ^" is declared");
    Option.iter (fun export -> vernac_import export [Ident (dummy_loc,id)]) export

let vernac_define_module export (loc, id) binders_ast mty_ast_o mexpr_ast_o = 
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Lib.sections_are_opened () then
    error "Modules and Module Types are not allowed inside sections.";
  match mexpr_ast_o with
    | None ->
       check_no_pending_proofs ();
       let binders_ast,argsexport =
        List.fold_right
         (fun (export,idl,ty) (args,argsexport) ->
           (idl,ty)::args, (List.map (fun (_,i) -> export,i)idl)@argsexport) binders_ast
             ([],[]) in
       let mp = Declaremods.start_module Modintern.interp_modtype export
	 id binders_ast mty_ast_o 
       in
	 Dumpglob.dump_moddef loc mp "mod";
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
       let mp =	Declaremods.declare_module 
	  Modintern.interp_modtype Modintern.interp_modexpr
	  id binders_ast mty_ast_o mexpr_ast_o 
       in
	 Dumpglob.dump_moddef loc mp "mod";
	 if_verbose message 
	   ("Module "^ string_of_id id ^" is defined");
         Option.iter (fun export -> vernac_import export [Ident (dummy_loc,id)])
           export

let vernac_end_module export (loc,id) =
  let mp = Declaremods.end_module id in
    Dumpglob.dump_modref loc mp "mod";
    if_verbose message ("Module "^ string_of_id id ^" is defined") ;
    Option.iter (fun export -> vernac_import export [Ident (dummy_loc,id)]) export


let vernac_declare_module_type (loc,id) binders_ast mty_ast_o =
  if Lib.sections_are_opened () then
    error "Modules and Module Types are not allowed inside sections.";
  
  match mty_ast_o with
    | None ->
       check_no_pending_proofs ();
       let binders_ast,argsexport =
        List.fold_right
         (fun (export,idl,ty) (args,argsexport) ->
           (idl,ty)::args, List.map (fun (_,i) -> export,i) idl) binders_ast
             ([],[]) in
       let mp = Declaremods.start_modtype Modintern.interp_modtype id binders_ast in
        Dumpglob.dump_moddef loc mp "modtype";
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
	let mp = Declaremods.declare_modtype Modintern.interp_modtype 
	  id binders_ast base_mty in
          Dumpglob.dump_moddef loc mp "modtype";
	  if_verbose message 
	    ("Module Type "^ string_of_id id ^" is defined")


let vernac_end_modtype (loc,id) =
  let mp = Declaremods.end_modtype id in
    Dumpglob.dump_modref loc mp "modtype";
    if_verbose message 
      ("Module Type "^ string_of_id id ^" is defined")

let vernac_include = function
  | CIMTE mty_ast ->
      Declaremods.declare_include Modintern.interp_modtype mty_ast false
  | CIME mexpr_ast ->
      Declaremods.declare_include Modintern.interp_modexpr mexpr_ast true
	  
	  
	  
(**********************)
(* Gallina extensions *)

  (* Sections *)

let vernac_begin_section (_, id as lid) =
  check_no_pending_proofs ();
  Dumpglob.dump_definition lid true "sec";
  Lib.open_section id

let vernac_end_section (loc, id) = 
  
    Dumpglob.dump_reference loc 
      (string_of_dirpath (Lib.current_dirpath true)) "<>" "sec";
  Lib.close_section id

let vernac_end_segment lid =
  check_no_pending_proofs ();
  let o = try Lib.what_is_opened () with 
      Not_found -> error "There is nothing to end." in
    match o with
      | _,Lib.OpenedModule (export,_,_) -> vernac_end_module export lid
      | _,Lib.OpenedModtype _ -> vernac_end_modtype lid
      | _,Lib.OpenedSection _ -> vernac_end_section lid
      | _ -> anomaly "No more opened things"

let vernac_require import _ qidl =
  let qidl = List.map qualid_of_reference qidl in
  let modrefl = List.map Library.try_locate_qualified_library qidl in
(*   let modrefl = List.map (fun qid -> let (dp, _) = (Library.try_locate_qualified_library qid) in dp) qidl in *)
    if Dumpglob.dump () then
      List.iter2 (fun (loc, _) dp -> Dumpglob.dump_libref loc dp "lib") qidl (List.map fst modrefl);
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

(* Type classes *)
 
let vernac_instance glob sup inst props pri =
  Dumpglob.dump_constraint inst false "inst";
  ignore(Classes.new_instance ~global:glob sup inst props pri)

let vernac_context l =
  List.iter (fun x -> Dumpglob.dump_local_binder x true "var") l;
  Classes.context l

let vernac_declare_instance id =
  Dumpglob.dump_definition id false "inst";
  Classes.declare_instance false id

(***********)
(* Solving *)
let vernac_solve n tcom b =
  if not (refining ()) then
    error "Unknown command of the non proof-editing mode.";
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
    error "Unknown command of the non proof-editing mode.";
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

let vernac_create_hintdb local id b = 
  Auto.create_hint_db local id full_transparent_state b

let vernac_hints = Auto.add_hints

let vernac_syntactic_definition lid =
  Dumpglob.dump_definition lid false "syndef";
  Command.syntax_definition (snd lid)
  
let vernac_declare_implicits local r = function
  | Some imps ->
      Impargs.declare_manual_implicits local (global_with_alias r) ~enriching:false
	(List.map (fun (ex,b,f) -> ex, (b,f)) imps)
  | None -> 
      Impargs.declare_implicits local (global_with_alias r)

let vernac_reserve idl c =
  let t = Constrintern.interp_type Evd.empty (Global.env()) c in
  let t = Detyping.detype false [] [] t in
  List.iter (fun id -> Reserve.declare_reserved_type id t) idl

let make_silent_if_not_pcoq b =
  if !pcoq <> None then 
    error "Turning on/off silent flag is not supported in Pcoq mode."
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
      optname  = "manual implicit arguments";
      optkey   = (TertiaryTable ("Manual","Implicit","Arguments"));
      optread  = Impargs.is_manual_implicit_args;
      optwrite = Impargs.make_manual_implicit_args }

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

(* let _ = *)
(*   declare_bool_option  *)
(*     { optsync  = true; *)
(*       optname  = "forceable implicit arguments"; *)
(*       optkey   = (SecondaryTable ("Forceable","Implicit")); *)
(*       optread  = Impargs.is_forceable_implicit_args; *)
(*       optwrite = Impargs.make_forceable_implicit_args } *)

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "implicit status of reversible patterns";
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
      optname  = "printing of existential variable instances";
      optkey   = (TertiaryTable ("Printing","Existential","Instances"));
      optread  = (fun () -> !Constrextern.print_evar_arguments);
      optwrite = (:=) Constrextern.print_evar_arguments }
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
      optname="printing of universes";
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

let vernac_set_opacity local str =
  let glob_ref r =
    match global_with_alias r with
      | ConstRef sp -> EvalConstRef sp
      | VarRef id -> EvalVarRef id
      | _ -> error
          "cannot set an inductive type or a constructor as transparent" in
  let str = List.map (fun (lev,ql) -> (lev,List.map glob_ref ql)) str in
  Redexpr.set_strategy local str

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
  | PrintTypeClasses -> ppnl (Prettyp.print_typeclasses())
  | PrintInstances c -> ppnl (Prettyp.print_instances (global c))
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
      msg (Printer.pr_assumptionset (Global.env ()) nassumptions)

let global_module r =
  let (loc,qid) = qualid_of_reference r in
  try Nametab.full_name_module qid
  with Not_found -> 
    user_err_loc (loc, "global_module",
      str "Module/section " ++ pr_qualid qid ++ str " not found.")

let interp_search_restriction = function
  | SearchOutside l -> (List.map global_module l, true)
  | SearchInside l -> (List.map global_module l, false)

open Search

let is_ident s = try ignore (check_ident s); true with UserError _ -> false

let interp_search_about_item = function
  | SearchSubPattern pat ->
      let _,pat = intern_constr_pattern Evd.empty (Global.env()) pat in
      GlobSearchSubPattern pat
  | SearchString (s,None) when is_ident s ->
      GlobSearchString s
  | SearchString (s,sc) ->
      try 
	let ref =
	  Notation.interp_notation_as_global_reference dummy_loc
	    (fun _ -> true) s sc in
	GlobSearchSubPattern (Pattern.PRef ref)
      with UserError _ -> 
	error ("Unable to interp \""^s^"\" either as a reference or
          	as an identifier component")

let vernac_search s r =
  let r = interp_search_restriction r in
  if !pcoq <> None then (Option.get !pcoq).search s r else
  match s with
  | SearchPattern c ->
      let _,pat = intern_constr_pattern Evd.empty (Global.env()) c in
      Search.search_pattern pat r
  | SearchRewrite c ->
      let _,pat = intern_constr_pattern Evd.empty (Global.env()) c in
      Search.search_rewrite pat r
  | SearchHead ref ->
      Search.search_by_head (global_with_alias ref) r
  | SearchAbout sl ->
      Search.search_about (List.map (on_snd interp_search_about_item) sl) r

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
        start_proof_com (Global, Proof unnamed_kind) [None,c] (fun _ _ ->());
	print_subgoals ()
      end else 
	error "repeated Goal not permitted in refining mode."

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
    error "No proof-editing in progress."

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
  msg (apply_subproof (fun evd _ -> print_treescript evd) occ)

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
      (str ("Condition violated: ") ++s)
  in 
  msgnl message

let interp c = match c with
  (* Control (done in vernac) *)
  | (VernacTime _ | VernacList _ | VernacLoad _) -> assert false

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
  | VernacDefinition (k,lid,d,f) -> vernac_definition k lid d f
  | VernacStartTheoremProof (k,l,top,f) -> vernac_start_proof k l top f
  | VernacEndProof e -> vernac_end_proof e
  | VernacExactProof c -> vernac_exact_proof c
  | VernacAssumption (stre,nl,l) -> vernac_assumption stre l nl
  | VernacInductive (finite,l) -> vernac_inductive finite l
  | VernacFixpoint (l,b) -> vernac_fixpoint l b
  | VernacCoFixpoint (l,b) -> vernac_cofixpoint l b
  | VernacScheme l -> vernac_scheme l
  | VernacCombinedScheme (id, l) -> vernac_combined_scheme id l

  (* Modules *)
  | VernacDeclareModule (export,lid,bl,mtyo) -> 
      vernac_declare_module export lid bl mtyo
  | VernacDefineModule (export,lid,bl,mtyo,mexpro) -> 
      vernac_define_module export lid bl mtyo mexpro
  | VernacDeclareModuleType (lid,bl,mtyo) -> 
      vernac_declare_module_type lid bl mtyo
  | VernacInclude (in_ast) ->
      vernac_include in_ast
  (* Gallina extensions *)
  | VernacBeginSection lid -> vernac_begin_section lid

  | VernacEndSegment lid -> vernac_end_segment lid

  | VernacRequire (export,spec,qidl) -> vernac_require export spec qidl
  | VernacImport (export,qidl) -> vernac_import export qidl
  | VernacCanonical qid -> vernac_canonical qid
  | VernacCoercion (str,r,s,t) -> vernac_coercion str r s t
  | VernacIdentityCoercion (str,(_,id),s,t) -> vernac_identity_coercion str id s t

  (* Type classes *)
  | VernacInstance (glob, sup, inst, props, pri) -> vernac_instance glob sup inst props pri
  | VernacContext sup -> vernac_context sup
  | VernacDeclareInstance id -> vernac_declare_instance id

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
  | VernacRemoveName id -> Lib.remove_name id
  | VernacResetName id -> vernac_reset_name id
  | VernacResetInitial -> vernac_reset_initial ()
  | VernacBack n -> vernac_back n
  | VernacBackTo n -> vernac_backto n

  (* Commands *)
  | VernacDeclareTacticDefinition (x,l) -> vernac_declare_tactic_definition x l
  | VernacCreateHintDb (local,dbname,b) -> vernac_create_hintdb local dbname b
  | VernacHints (local,dbnames,hints) -> vernac_hints local dbnames hints
  | VernacSyntacticDefinition (id,c,l,b) ->vernac_syntactic_definition id c l b
  | VernacDeclareImplicits (local,qid,l) ->vernac_declare_implicits local qid l
  | VernacReserve (idl,c) -> vernac_reserve idl c
  | VernacSetOpacity (local,qidl) -> vernac_set_opacity local qidl
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
  | VernacGoal t -> vernac_start_proof Theorem [None,([],t)] false (fun _ _->())
  | VernacAbort id -> vernac_abort id
  | VernacAbortAll -> vernac_abort_all ()
  | VernacRestart -> vernac_restart ()
  | VernacSuspend -> vernac_suspend ()
  | VernacResume id -> vernac_resume id
  | VernacUndo n -> vernac_undo n
  | VernacUndoTo n -> undo_todepth n
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
