(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Vernac
open Vernacexpr
open Pfedit
open Pp
open Util
open Names
open Term
open Printer
open Environ
open Evarutil
open Evd
open Decl_mode
open Hipattern
open Tacmach
open Reductionops
open Termops
open Ideutils

let prerr_endline s = if !debug then prerr_endline s else ()

let output = ref (Format.formatter_of_out_channel stdout)

let msg m = 
  let b =  Buffer.create 103 in
  Pp.msg_with (Format.formatter_of_buffer b) m;
  Buffer.contents b

let msgnl m = 
  (msg m)^"\n"

let init () = 
  (* To hide goal in lower window. 
     Problem: should not hide "xx is assumed"
     messages *)
(**)
  Flags.make_silent true;
(**)
  Coqtop.init_ide ()


let i = ref 0

let version () =
  let date =
    if Glib.Utf8.validate Coq_config.date
    then Coq_config.date
    else "<date not printable>" in
  let get_version_date () =
    try
      let ch = open_in (Coq_config.coqtop^"/revision") in
      let ver = input_line ch in
      let rev = input_line ch in
	(ver,rev)
    with _ -> (Coq_config.version,date) in
  let (rev,ver) = get_version_date () in
    Printf.sprintf 
      "The Coq Proof Assistant, version %s (%s)\
       \nArchitecture %s running %s operating system\
       \nGtk version is %s\
       \nThis is the %s version (%s is the best one for this architecture and OS)\
       \n"
      rev ver
      Coq_config.arch Sys.os_type
      (let x,y,z = GMain.Main.version in Printf.sprintf "%d.%d.%d" x y z)
    (if Mltop.get () = Mltop.Native then "native" else "bytecode") 
    (if Coq_config.best="opt" then "native" else "bytecode") 

let is_in_coq_lib dir = 
  prerr_endline ("Is it a coq theory ? : "^dir);
  let is_same_file = same_file dir in
  List.exists 
    (fun s -> 
      let fdir =
        Filename.concat Coq_config.coqlib (Filename.concat "theories" s) in
      prerr_endline (" Comparing to: "^fdir);
      if is_same_file fdir then (prerr_endline " YES";true)
      else (prerr_endline"NO";false))
    Coq_config.theories_dirs

let is_in_loadpath dir =
  Library.is_in_load_paths (System.physical_path_of_string dir)

let is_in_coq_path f = 
  try 
  let base = Filename.chop_extension (Filename.basename f) in
  let _ = Library.locate_qualified_library 
	    (Libnames.make_qualid Names.empty_dirpath 
	       (Names.id_of_string base)) in
  prerr_endline (f ^ " is in coq path");
  true
  with _ ->  
    prerr_endline (f ^ " is NOT in coq path");
    false  

let is_in_proof_mode () = 
  match Decl_mode.get_current_mode () with
      Decl_mode.Mode_none -> false
    | _ -> true

let user_error_loc l s =
  raise (Stdpp.Exc_located (l, Util.UserError ("CoqIde", s)))

type printing_state = {
  mutable printing_implicit : bool;
  mutable printing_coercions : bool;
  mutable printing_raw_matching : bool;
  mutable printing_no_notation : bool;
  mutable printing_all : bool;
  mutable printing_evar_instances : bool;
  mutable printing_universes : bool
}

let printing_state = {
  printing_implicit = false;
  printing_coercions = false;
  printing_raw_matching = false;
  printing_no_notation = false;
  printing_all = false;
  printing_evar_instances = false;
  printing_universes = false;
}

let printing_implicit_data = ["Printing";"Implicit"], false
let printing_coercions_data = ["Printing";"Coercions"], false
let printing_raw_matching_data = ["Printing";"Matching"], true
let printing_no_synth_data = ["Printing";"Synth"], true
let printing_no_notation_data = ["Printing";"Notations"], true
let printing_all_data = ["Printing";"All"], false
let printing_evar_instances_data = ["Printing";"Existential";"Instances"],false
let printing_universes_data = ["Printing";"Universes"], false

let known_options = ref []

let prepare_option (l,dft) =
  known_options := l :: !known_options;
  let set = (String.concat " " ("Set"::l)) ^ "." in
  let unset = (String.concat " " ("Unset"::l)) ^ "." in
  if dft then unset,set else set,unset

let coqide_known_option = function
  | Goptions.TertiaryTable (a,b,c) -> List.mem [a;b;c] !known_options
  | Goptions.SecondaryTable (a,b) -> List.mem [a;b] !known_options
  | Goptions.PrimaryTable a -> List.mem [a] !known_options

let with_printing_implicit = prepare_option printing_implicit_data
let with_printing_coercions = prepare_option printing_coercions_data
let with_printing_raw_matching = prepare_option printing_raw_matching_data
let with_printing_no_synth = prepare_option printing_no_synth_data
let with_printing_no_notation = prepare_option printing_no_notation_data
let with_printing_all = prepare_option printing_all_data
let with_printing_evar_instances = prepare_option printing_evar_instances_data
let with_printing_universes = prepare_option printing_universes_data

let make_option_commands () =
  let p = printing_state in
  (if p.printing_implicit then [with_printing_implicit] else [])@
  (if p.printing_coercions then [with_printing_coercions] else [])@
  (if p.printing_raw_matching then [with_printing_raw_matching;with_printing_no_synth] else [])@
  (if p.printing_no_notation then [with_printing_no_notation] else [])@
  (if p.printing_all then [with_printing_all] else [])@
  (if p.printing_evar_instances then [with_printing_evar_instances] else [])@
  (if p.printing_universes then [with_printing_universes] else [])

let make_option_commands () =
  let l = make_option_commands () in
  List.iter (fun (a,b) -> prerr_endline a; prerr_endline b) l;
  l

type command_attribute =
    NavigationCommand | QueryCommand | DebugCommand | KnownOptionCommand
  | OtherStatePreservingCommand | GoalStartingCommand | SolveCommand

let rec attribute_of_vernac_command = function
  (* Control *)
  | VernacTime com -> attribute_of_vernac_command com
  | VernacList _ -> [] (* unsupported *)
  | VernacLoad _ -> []

  (* Syntax *)
  | VernacTacticNotation _ -> []
  | VernacSyntaxExtension _ -> []
  | VernacDelimiters _ -> []
  | VernacBindScope _ -> []
  | VernacOpenCloseScope _ -> []
  | VernacArgumentsScope _ -> []
  | VernacInfix _ -> []
  | VernacNotation _ -> []

  (* Gallina *)
  | VernacDefinition (_,_,DefineBody _,_) -> []
  | VernacDefinition (_,_,ProveBody _,_) -> [GoalStartingCommand]
  | VernacStartTheoremProof _ -> [GoalStartingCommand]
  | VernacEndProof _ -> []
  | VernacExactProof _ -> []

  | VernacAssumption _ -> []
  | VernacInductive _ -> []
  | VernacFixpoint _ -> []
  | VernacCoFixpoint _ -> []
  | VernacScheme _ -> []
  | VernacCombinedScheme _ -> []

  (* Modules *)
  | VernacDeclareModule _ -> []
  | VernacDefineModule _  -> []
  | VernacDeclareModuleType _ -> []
  | VernacInclude _ -> []

  (* Gallina extensions *)
  | VernacBeginSection _ -> []
  | VernacEndSegment _ -> []
  | VernacRecord _ -> []
  | VernacRequire _ -> []
  | VernacImport _ -> []
  | VernacCanonical _ -> []
  | VernacCoercion _ -> []
  | VernacIdentityCoercion _ -> []

  (* Type classes *)
  | VernacClass _ -> []
  | VernacInstance _ -> []
  | VernacContext _ -> []
  | VernacDeclareInstance _ -> []

  (* Solving *)
  | VernacSolve _ -> [SolveCommand]
  | VernacSolveExistential _ -> [SolveCommand]

  (* MMode *)
  | VernacDeclProof -> []
  | VernacReturn -> []
  | VernacProofInstr _ -> []

  (* Auxiliary file and library management *)
  | VernacRequireFrom _ -> []
  | VernacAddLoadPath _ -> []
  | VernacRemoveLoadPath _ -> []
  | VernacAddMLPath _ -> []
  | VernacDeclareMLModule _ -> []
  | VernacChdir _ -> [OtherStatePreservingCommand]

  (* State management *)
  | VernacWriteState _ -> []
  | VernacRestoreState _ -> []

  (* Resetting *)
  | VernacRemoveName _ -> [NavigationCommand]
  | VernacResetName _ -> [NavigationCommand]
  | VernacResetInitial -> [NavigationCommand]
  | VernacBack _ -> [NavigationCommand]
  | VernacBackTo _ -> [NavigationCommand]

  (* Commands *)
  | VernacDeclareTacticDefinition _ -> []
  | VernacHints _ -> []
  | VernacSyntacticDefinition _ -> []
  | VernacDeclareImplicits _ -> []
  | VernacReserve _ -> []
  | VernacSetOpacity _ -> []
  | VernacSetOption (Goptions.SecondaryTable ("Ltac","Debug"), _) -> 
      [DebugCommand]
  | VernacSetOption (o,BoolValue true) | VernacUnsetOption o ->
      if coqide_known_option o then [KnownOptionCommand] else []
  | VernacSetOption _ -> []
  | VernacRemoveOption _ -> []
  | VernacAddOption _ -> []
  | VernacMemOption _ -> [QueryCommand]

  | VernacPrintOption _ -> [QueryCommand]
  | VernacCheckMayEval _ -> [QueryCommand]
  | VernacGlobalCheck _ -> [QueryCommand]
  | VernacPrint _ -> [QueryCommand]
  | VernacSearch _ -> [QueryCommand]
  | VernacLocate _ -> [QueryCommand]

  | VernacComments _ -> [OtherStatePreservingCommand]
  | VernacNop -> [OtherStatePreservingCommand]

  (* Proof management *)
  | VernacGoal _ -> [GoalStartingCommand]

  | VernacAbort _ -> [NavigationCommand]
  | VernacAbortAll -> [NavigationCommand]
  | VernacRestart -> [NavigationCommand]
  | VernacSuspend -> [NavigationCommand]
  | VernacResume _ -> [NavigationCommand]
  | VernacUndo _ -> [NavigationCommand]
  | VernacUndoTo _ -> [NavigationCommand]
  | VernacBacktrack _ -> [NavigationCommand]

  | VernacFocus _ -> [SolveCommand]
  | VernacUnfocus -> [SolveCommand]
  | VernacGo _ -> []
  | VernacShow _ -> [OtherStatePreservingCommand]
  | VernacCheckGuard -> [OtherStatePreservingCommand]
  | VernacProof (Tacexpr.TacId []) -> [OtherStatePreservingCommand]
  | VernacProof _ -> []

  (* Toplevel control *)
  | VernacToplevelControl _ -> []

  (* Extensions *)
  | VernacExtend ("Subtac_Obligations", _) -> [GoalStartingCommand]
  | VernacExtend _ -> []

let is_vernac_goal_starting_command com =
  List.mem GoalStartingCommand (attribute_of_vernac_command com)

let is_vernac_navigation_command com =
  List.mem NavigationCommand (attribute_of_vernac_command com)

let is_vernac_query_command com =
  List.mem QueryCommand (attribute_of_vernac_command com)

let is_vernac_known_option_command com =
  List.mem KnownOptionCommand (attribute_of_vernac_command com)

let is_vernac_debug_command com =
  List.mem DebugCommand (attribute_of_vernac_command com)

let is_vernac_goal_printing_command com =
  let attribute = attribute_of_vernac_command com in
  List.mem GoalStartingCommand attribute or
  List.mem SolveCommand attribute

let is_vernac_state_preserving_command com =
  let attribute = attribute_of_vernac_command com in
  List.mem OtherStatePreservingCommand attribute or
  List.mem QueryCommand attribute

let is_vernac_tactic_command com =
  List.mem SolveCommand (attribute_of_vernac_command com)

type reset_mark =
  | ResetToId of Names.identifier
  | ResetToState of  Libnames.object_name

type reset_info =
  | NoReset
  | ResetAtDecl of reset_mark * bool ref
  | ResetAtSegmentStart of Names.identifier * bool ref 
  | ResetAtFrozenState of Libnames.object_name * bool ref

let reset_mark id = match Lib.has_top_frozen_state () with
  | Some sp -> ResetToState sp
  | None -> ResetToId id

let compute_reset_info = function 
  | VernacBeginSection id 
  | VernacDefineModule (_,id, _, _, _) 
  | VernacDeclareModule (_,id, _, _)
  | VernacDeclareModuleType (id, _, _) ->
      ResetAtSegmentStart (snd id, ref true)

  | VernacDefinition (_, (_,id), DefineBody _, _)
  | VernacAssumption (_,_ ,(_,((_,id)::_,_))::_)
  | VernacInductive (_, (((_,id),_,_,_),_) :: _) ->
      ResetAtDecl (reset_mark id, ref true)

  | VernacDefinition (_, (_,id), ProveBody _, _)
  | VernacStartTheoremProof (_, [Some (_,id), _], _, _) ->
      ResetAtDecl (reset_mark id, ref false)

  | VernacEndProof _ -> NoReset
  | _ -> match Lib.has_top_frozen_state () with
      | Some sp -> ResetAtFrozenState (sp, ref true)
      | None -> NoReset

let reset_initial () = 
  prerr_endline "Reset initial called"; flush stderr;
  Vernacentries.abort_refine Lib.reset_initial ()

let reset_to = function
  | ResetToId id ->
      prerr_endline ("Reset called with "^(string_of_id id));
      Vernacentries.abort_refine Lib.reset_name (Util.dummy_loc,id)
  | ResetToState sp ->
      prerr_endline
        ("Reset called with state "^(Libnames.string_of_path (fst sp)));
      Vernacentries.abort_refine Lib.reset_to_state sp

let reset_to_mod id = 
  prerr_endline ("Reset called to Mod/Sect with "^(string_of_id id)); 
  Vernacentries.abort_refine Lib.reset_mod (Util.dummy_loc,id)

let raw_interp s =
  Vernac.raw_do_vernac (Pcoq.Gram.parsable (Stream.of_string s))

let interp_with_options verbosely options s = 
  prerr_endline "Starting interp...";
  prerr_endline s;
  let pa = Pcoq.Gram.parsable (Stream.of_string s) in
  let pe = Pcoq.Gram.Entry.parse Pcoq.main_entry pa in
  match pe with 
    | None -> assert false
    | Some((loc,vernac) as last) ->
	if is_vernac_goal_starting_command vernac & is_in_proof_mode () then
	  user_error_loc loc (str "CoqIDE do not support nested goals");
	if is_vernac_debug_command vernac then
	  user_error_loc loc (str "Debug mode not available within CoqIDE");
	if is_vernac_navigation_command vernac then
	  user_error_loc loc (str "Use CoqIDE navigation instead");
	if is_vernac_known_option_command vernac then
	  user_error_loc loc (str "Use CoqIDE buttons instead");
	if is_vernac_query_command vernac then 
	  !flash_info
	    "Warning: query commands should not be inserted in scripts";
	if not (is_vernac_goal_printing_command vernac) then
	  (* Verbose if in small step forward and not a tactic *)
	  Flags.make_silent (not verbosely);
	let reset_info = compute_reset_info vernac in
	List.iter (fun (set_option,_) -> raw_interp set_option) options;
	raw_interp s;
	Flags.make_silent true;
	List.iter (fun (_,unset_option) -> raw_interp unset_option) options;
	prerr_endline ("...Done with interp of : "^s);
	reset_info,last

let interp verbosely phrase =
  interp_with_options verbosely (make_option_commands ()) phrase

let interp_and_replace s = 
  let result = interp false s in
  let msg = read_stdout () in
  result,msg

let nb_subgoals pf =
  List.length (fst (Refiner.frontier (Tacmach.proof_of_pftreestate pf)))

type tried_tactic = 
  | Interrupted
  | Success of int (* nb of goals after *)
  | Failed

let try_interptac s = 
  try
    prerr_endline ("Starting try_interptac: "^s);
    let pf = get_pftreestate () in
    let pe = Pcoq.Gram.Entry.parse 
	       Pcoq.main_entry 
	       (Pcoq.Gram.parsable (Stream.of_string s)) 
    in match pe with 
    | Some (loc,(VernacSolve (n, tac, _))) ->
	let tac = Tacinterp.interp tac in
	let pf' = solve_nth_pftreestate n tac pf in
	prerr_endline "Success";
	let nb_goals = nb_subgoals pf' - nb_subgoals pf in
	Success nb_goals
    | _ ->
	prerr_endline "try_interptac: not a tactic"; Failed
  with 
  | Sys.Break | Stdpp.Exc_located (_,Sys.Break)
      -> prerr_endline "try_interp: interrupted"; Interrupted
  | Stdpp.Exc_located (_,e) -> prerr_endline ("try_interp: failed ("^(Printexc.to_string e)); Failed
  | e -> Failed	  

let rec is_pervasive_exn = function
  | Out_of_memory | Stack_overflow | Sys.Break -> true
  | Error_in_file (_,_,e) -> is_pervasive_exn e
  | Stdpp.Exc_located (_,e) -> is_pervasive_exn e
  | DuringCommandInterp (_,e) -> is_pervasive_exn e
  | _ -> false

let print_toplevel_error exc =
  let (dloc,exc) =
    match exc with
      | DuringCommandInterp (loc,ie) ->
          if loc = dummy_loc then (None,ie) else (Some loc, ie)
      | _ -> (None, exc) 
  in
  let (loc,exc) =
    match exc with
      | Stdpp.Exc_located (loc, ie) -> (Some loc),ie
      | Error_in_file (s, (_,fname, loc), ie) -> None, ie
      | _ -> dloc,exc
  in
  match exc with
    | End_of_input  -> 	str "Please report: End of input",None
    | Vernacexpr.ProtectedLoop -> 
	str "ProtectedLoop  not allowed by coqide!",None
    | Vernacexpr.Drop ->  str "Drop is not allowed by coqide!",None
    | Vernacexpr.Quit -> str "Quit is not allowed by coqide! Use menus.",None
    | _ -> 
	(try Cerrors.explain_exn exc with e -> 
	   str "Failed to explain error. This is an internal Coq error. Please report.\n"
	   ++ str (Printexc.to_string  e)),
	(if is_pervasive_exn exc then None else loc)

let process_exn e = let s,loc= print_toplevel_error e in (msgnl s,loc)

let interp_last last = 
  prerr_string "*";
  try
    vernac_com (States.with_heavy_rollback Vernacentries.interp) last
  with e ->
    let s,_ = process_exn e in prerr_endline ("Replay during undo failed because: "^s);
    raise e


type hyp = env * evar_map *
           ((identifier * string) * constr option * constr) * 
           (string * string)
type concl = env * evar_map * constr * string
type meta = env * evar_map * string
type goal = hyp list * concl

let prepare_hyp sigma env ((i,c,d) as a) =
  env, sigma,
  ((i,string_of_id i),c,d), 
  (msg (pr_var_decl env a), msg (pr_ltype_env env d))

let prepare_hyps sigma env =
  assert (rel_context env = []);
  let hyps =
    fold_named_context
      (fun env d acc -> let hyp = prepare_hyp sigma env d in hyp :: acc)
      env ~init:[] 
  in
  List.rev hyps

let prepare_goal_main sigma g =
  let env = evar_env g in
  (prepare_hyps sigma env,
   (env, sigma, g.evar_concl, msg (pr_ltype_env_at_top env g.evar_concl)))

let prepare_goal sigma g =
  let options = make_option_commands () in
  List.iter (fun (set_option,_) -> raw_interp set_option) options;
  let x = prepare_goal_main sigma g in
  List.iter (fun (_,unset_option) -> raw_interp unset_option) options;
  x

let get_current_pm_goal () =
  let pfts = get_pftreestate ()  in
  let gls = try nth_goal_of_pftreestate 1 pfts with _ -> raise Not_found in
  let sigma= sig_sig gls in
  let gl = sig_it gls in
    prepare_goal sigma gl


let get_current_goals () = 
    let pfts = get_pftreestate () in
    let gls = fst (Refiner.frontier (Tacmach.proof_of_pftreestate pfts)) in 
    let sigma = Tacmach.evc_of_pftreestate pfts in
    List.map (prepare_goal sigma) gls

let get_current_goals_nb () = 
  try List.length (get_current_goals ()) with _ -> 0
  
let print_no_goal () =
    let pfts = get_pftreestate () in
    let gls = fst (Refiner.frontier (Tacmach.proof_of_pftreestate pfts)) in 
    assert (gls = []);
    let sigma = Tacmach.project (Tacmach.top_goal_of_pftreestate pfts) in
    msg (Printer.pr_subgoals (Decl_mode.get_end_command pfts) sigma gls)


let hyp_menu (env, sigma, ((coqident,ident),_,ast),(s,pr_ast)) =
  [("clear "^ident),("clear "^ident^".");
   
   ("apply "^ident),
   ("apply "^ident^".");
   
   ("exact "^ident),
   ("exact "^ident^".");

   ("generalize "^ident),
   ("generalize "^ident^".");
   
   ("absurd <"^ident^">"),
   ("absurd "^
    pr_ast
    ^".") ] @

   (if is_equation ast then
      [ "discriminate "^ident, "discriminate "^ident^".";
	"injection "^ident, "injection "^ident^"." ]
    else
      []) @
   
   (let _,t = splay_prod env sigma ast in
    if is_equation t then 
      [ "rewrite "^ident, "rewrite "^ident^".";
	"rewrite <- "^ident, "rewrite <- "^ident^"." ]
    else
      []) @
   
  [("elim "^ident),
   ("elim "^ident^".");
   
   ("inversion "^ident),
   ("inversion "^ident^".");
   
   ("inversion clear "^ident),
   ("inversion_clear "^ident^".")] 

let concl_menu (_,_,concl,_) = 
  let is_eq = is_equation concl in
  ["intro", "intro.";
   "intros", "intros.";
   "intuition","intuition." ] @
   
   (if is_eq then 
      ["reflexivity", "reflexivity.";
       "discriminate", "discriminate.";
       "symmetry", "symmetry." ]
    else 
      []) @

  ["assumption" ,"assumption.";
   "omega", "omega.";
   "ring", "ring.";
   "auto with *", "auto with *.";
   "eauto with *", "eauto with *.";
   "tauto", "tauto.";
   "trivial", "trivial.";
   "decide equality", "decide equality.";

   "simpl", "simpl.";
   "subst", "subst.";

   "red", "red.";
   "split", "split.";
   "left", "left.";
   "right", "right.";
  ]


let id_of_name = function 
  | Names.Anonymous -> id_of_string "x" 
  | Names.Name x -> x

let make_cases s = 
  let qualified_name = Libnames.qualid_of_string s in
  let glob_ref = Nametab.locate qualified_name in
  match glob_ref with
    | Libnames.IndRef i -> 
	let {Declarations.mind_nparams = np},
	{Declarations.mind_consnames = carr ;
	 Declarations.mind_nf_lc = tarr } 
	= Global.lookup_inductive i 
	in
	Util.array_fold_right2 
	  (fun n t l ->  
	     let (al,_) = Term.decompose_prod t in
	     let al,_ = Util.list_chop (List.length al - np) al in
	     let rec rename avoid = function 
	       | [] -> []
	       | (n,_)::l -> 
		   let n' = next_global_ident_away true
			      (id_of_name n) 
			      avoid
		   in (string_of_id n')::(rename (n'::avoid) l)
	     in
	     let al' = rename [] (List.rev al) in
	     (string_of_id n :: al') :: l
	  )
	  carr 
	  tarr
	  []
    | _ -> raise Not_found

let current_status () = 
  let path = msg (Libnames.pr_dirpath (Lib.cwd ())) in
  let path = if path = "Top" then "Ready" else "Ready in " ^ String.sub path 4 (String.length path - 4) in
  try
    path ^ ", proving " ^ (Names.string_of_id (Pfedit.get_current_proof_name ()))
  with _ -> path
