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
  Options.make_silent true;
(**)
  Coqtop.init_ide ()


let i = ref 0

let version () =
  let date =
    if Glib.Utf8.validate Coq_config.date
    then Coq_config.date
    else "<date not printable>"
  in
  Printf.sprintf 
    "The Coq Proof Assistant, version %s (%s)\
   \nConfigured on %s\
   \nArchitecture %s running %s operating system\
   \nGtk version is %s\
   \nThis is the %s version (%s is the best one for this architecture and OS)\
   \n"
    Coq_config.version date Coq_config.compile_date
    Coq_config.arch Sys.os_type
    (let x,y,z = GMain.Main.version in Printf.sprintf "%d.%d.%d" x y z)
    (if Mltop.get () = Mltop.Native then "native" else "bytecode") 
    (if Coq_config.best="opt" then "native" else "bytecode") 

let is_in_coq_lib dir = 
  prerr_endline ("Is it a coq theory ? : "^dir);
  try
    let stat = Unix.stat dir in
      List.exists 
	(fun s -> 
	   try
	     let fdir = Filename.concat 
	       Coq_config.coqlib 
	       (Filename.concat "theories" s) 
	     in
	       prerr_endline (" Comparing to: "^fdir);
	       let fstat = Unix.stat fdir in 
		 (fstat.Unix.st_dev = stat.Unix.st_dev) &&
		   (fstat.Unix.st_ino = stat.Unix.st_ino) && 
		   (prerr_endline " YES";true)
	   with _ -> prerr_endline " No(because of a local exn)";false
	)
	Coq_config.theories_dirs
  with _ -> prerr_endline " No(because of a global exn)";false

let is_in_loadpath dir = Library.is_in_load_paths (System.physical_path_of_string dir)

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
  try ignore (get_pftreestate ()); true with _ -> false

let user_error_loc l s =
  raise (Stdpp.Exc_located (l, Util.UserError ("CoqIde", s)))

let interp verbosely s = 
  prerr_endline "Starting interp...";
  prerr_endline s;
  let pa = Pcoq.Gram.parsable (Stream.of_string s) in
  let pe = Pcoq.Gram.Entry.parse Pcoq.main_entry pa in
  match pe with 
    | None -> assert false
    | Some((loc,vernac) as last) ->
	match vernac with
	  | VernacDefinition _  | VernacStartTheoremProof _ 
	  | VernacBeginSection _ | VernacGoal _
	  | VernacDefineModule _ | VernacDeclareModuleType _
	  | VernacDeclareTacticDefinition _
		when is_in_proof_mode () -> 
		  user_error_loc loc (str "CoqIDE do not support nested goals")
	  | VernacSetOption (Goptions.SecondaryTable ("Ltac","Debug"), _) ->
	      user_error_loc loc (str "Debug mode not available within CoqIDE")
	  | VernacResetName _
	  | VernacResetInitial 
	  | VernacBack _ 
	  | VernacAbort _ 
	  | VernacAbortAll
	  | VernacRestart
	  | VernacSuspend
	  | VernacResume _
	  | VernacUndo _ ->
	      user_error_loc loc (str "Use CoqIDE navigation instead") 
	  | _ ->
	      begin
		match vernac with
		  | VernacPrintOption _ 
		  | VernacCheckMayEval _
		  | VernacGlobalCheck _
		  | VernacPrint _
		  | VernacSearch _ 
		    -> !flash_info 
			"Warning: query commands should not be inserted in scripts" 
		  | VernacDefinition (_,_,DefineBody _,_) 
		  | VernacInductive _
		  | VernacFixpoint _
		  | VernacCoFixpoint _
		  | VernacEndProof _
		    -> Options.make_silent (not verbosely)
		  | _ -> ()
	      end;
	      Vernac.raw_do_vernac (Pcoq.Gram.parsable (Stream.of_string s));
	      Options.make_silent true;
	      prerr_endline ("...Done with interp of : "^s);
	      last

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

let is_tactic = function
  | VernacSolve _ -> true
  | _ -> false


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
type goal = hyp list * concl

let prepare_hyp sigma env ((i,c,d) as a) =
  env, sigma,
  ((i,string_of_id i),c,d), 
  (msg (pr_var_decl env a), msg (pr_lconstr_env_at_top env d))

let prepare_hyps sigma env =
  assert (rel_context env = []);
  let hyps =
    fold_named_context
      (fun env d acc -> let hyp = prepare_hyp sigma env d in hyp :: acc)
      env ~init:[] 
  in
  List.rev hyps

let prepare_goal sigma g =
  let env = evar_env g in
  (prepare_hyps sigma env,
   (env, sigma, g.evar_concl, msg (pr_lconstr_env_at_top env g.evar_concl)))

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
    msg (Printer.pr_subgoals sigma gls)


type word_class = Normal | Kwd | Reserved


let kwd = [(* "Compile";"Inductive";"Qed";"Type";"end";"Axiom";
	      "Definition";"Load";"Quit";"Variable";"in";"Cases";"FixPoint";
	      "Parameter";"Set";"of";"CoFixpoint";"Grammar";"Proof";"Syntax";
	      "using";"CoInductive";"Hypothesis";"Prop";"Theorem";
	   *)
  "Add"; "AddPath"; "Axiom"; "Chapter"; "CoFixpoint";
  "CoInductive"; "Defined"; "Definition"; 
  "End"; "Export"; "Fact"; "Fix"; "Fixpoint"; "Global"; "Grammar"; "Hint";
  "Hypothesis"; "Immediate"; "Implicits"; "Import"; "Inductive"; 
  "Infix"; "Lemma"; "Load"; "Local"; 
  "Match"; "Module"; "Module Type";
  "Mutual"; "Parameter"; "Print"; "Proof"; "Qed";
  "Record"; "Recursive"; "Remark"; "Require"; "Save"; "Scheme";
  "Section"; "Show"; "Syntactic"; "Syntax"; "Tactic"; "Theorem"; 
  "Unset"; "Variable"; "Variables"; 
]
	    
let reserved = []

module SHashtbl = 
  Hashtbl.Make 
    (struct 
       type t = string
       let equal = ( = )
       let hash = Hashtbl.hash
     end)


let word_tbl = SHashtbl.create 37
let _ = 
  List.iter (fun w -> SHashtbl.add word_tbl w Kwd) kwd;
  List.iter (fun w -> SHashtbl.add word_tbl w Reserved) reserved

let word_class s = 
  try
    SHashtbl.find word_tbl s
  with Not_found -> Normal

type reset_info = NoReset | Reset of Names.identifier * bool ref

let compute_reset_info = function 
  | VernacDefinition (_, (_,id), DefineBody _, _) 
  | VernacBeginSection (_,id) 
  | VernacDefineModule (_,(_,id), _, _, _) 
  | VernacDeclareModule (_,(_,id), _, _)
  | VernacDeclareModuleType ((_,id), _, _)
  | VernacAssumption (_, (_,((_,id)::_,_))::_)
  | VernacInductive (_, ((_,id),_,_,_,_) :: _) ->
      Reset (id, ref true)
  | VernacDefinition (_, (_,id), ProveBody _, _)
  | VernacStartTheoremProof (_, (_,id), _, _, _) ->
      Reset (id, ref false)
  | _ -> NoReset

let reset_initial () = 
  prerr_endline "Reset initial called"; flush stderr;
  Vernacentries.abort_refine Lib.reset_initial ()

let reset_to id = 
  prerr_endline ("Reset called with "^(string_of_id id));
  Vernacentries.abort_refine Lib.reset_name (Util.dummy_loc,id)
let reset_to_mod id = 
  prerr_endline ("Reset called to Mod/Sect with "^(string_of_id id)); 
  Vernacentries.abort_refine Lib.reset_mod (Util.dummy_loc,id)


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

let is_state_preserving = function
  | VernacPrint _ | VernacPrintOption _ | VernacGlobalCheck _
  | VernacCheckMayEval _ | VernacSearch _ | VernacLocate _ 
  | VernacShow _ | VernacMemOption _ | VernacComments _ 
  | VernacChdir None | VernacNop -> 
      prerr_endline "state preserving command found"; true
  | _ -> 
      false


let current_status () = 
  let path = msg (Libnames.pr_dirpath (Lib.cwd ())) in
  let path = if path = "Top" then "Ready" else "Ready in " ^ String.sub path 4 (String.length path - 4) in
  try
    path ^ ", proving " ^ (Names.string_of_id (Pfedit.get_current_proof_name ()))
  with _ -> path

  
