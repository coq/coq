(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
open Namegen
open Ideutils

type coqtop = unit

let dummy_coqtop = ()

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
  (* don't set a too large undo stack because Edit.create allocates an array *)
  Pfedit.set_undo (Some 5000);
(**)
  Coqtop.init_ide ()


let i = ref 0

let get_version_date () =
  let date =
    if Glib.Utf8.validate Coq_config.date
    then Coq_config.date
    else "<date not printable>" in
  try
    let ch = open_in (Coq_config.coqsrc^"/revision") in
    let ver = input_line ch in
    let rev = input_line ch in
    (ver,rev)
  with _ -> (Coq_config.version,date)

let short_version () =
  let (ver,date) = get_version_date () in
  Printf.sprintf "The Coq Proof Assistant, version %s (%s)\n" ver date

let version () =
  let (ver,date) = get_version_date () in
    Printf.sprintf
      "The Coq Proof Assistant, version %s (%s)\
       \nArchitecture %s running %s operating system\
       \nGtk version is %s\
       \nThis is the %s version (%s is the best one for this architecture and OS)\
       \n"
      ver date
      Coq_config.arch Sys.os_type
      (let x,y,z = GMain.Main.version in Printf.sprintf "%d.%d.%d" x y z)
    (if Mltop.is_native then "native" else "bytecode")
    (if Coq_config.best="opt" then "native" else "bytecode")

let is_in_loadpath coqtop dir =
  Library.is_in_load_paths (System.physical_path_of_string dir)

let user_error_loc l s =
  raise (Stdpp.Exc_located (l, Util.UserError ("CoqIde", s)))

let known_options = ref []

let prepare_option (l,dft) =
  known_options := l :: !known_options;
  let set = (String.concat " " ("Set"::l)) ^ "." in
  let unset = (String.concat " " ("Unset"::l)) ^ "." in
  if dft then unset,set else set,unset

let coqide_known_option table = List.mem table !known_options

type command_attribute =
    NavigationCommand | QueryCommand | DebugCommand | KnownOptionCommand
  | OtherStatePreservingCommand | GoalStartingCommand | SolveCommand
  | ProofEndingCommand

let rec attribute_of_vernac_command = function
  (* Control *)
  | VernacTime com -> attribute_of_vernac_command com
  | VernacTimeout(_,com) -> attribute_of_vernac_command com
  | VernacFail com -> attribute_of_vernac_command com
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
  | VernacEndProof _ -> [ProofEndingCommand]
  | VernacExactProof _ -> [ProofEndingCommand]

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
  | VernacRequire _ -> []
  | VernacImport _ -> []
  | VernacCanonical _ -> []
  | VernacCoercion _ -> []
  | VernacIdentityCoercion _ -> []

  (* Type classes *)
  | VernacInstance _ -> []
  | VernacContext _ -> []
  | VernacDeclareInstance _ -> []
  | VernacDeclareClass _ -> []

  (* Solving *)
  | VernacSolve _ -> [SolveCommand]
  | VernacSolveExistential _ -> [SolveCommand]

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
  | VernacCreateHintDb _ -> []
  | VernacHints _ -> []
  | VernacSyntacticDefinition _ -> []
  | VernacDeclareImplicits _ -> []
  | VernacDeclareReduction _ -> []
  | VernacReserve _ -> []
  | VernacGeneralizable _ -> []
  | VernacSetOpacity _ -> []
  | VernacSetOption (_,["Ltac";"Debug"], _) -> [DebugCommand]
  | VernacSetOption (_,o,BoolValue true) | VernacUnsetOption (_,o) ->
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

  | VernacProofMode _ -> []

  | VernacSubproof _ -> [SolveCommand]
  | VernacEndSubproof _ -> [SolveCommand]

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

let is_vernac_proof_ending_command com =
  List.mem ProofEndingCommand (attribute_of_vernac_command com)

type reset_status =
  | NoReset
  | ResetToNextMark
  | ResetAtMark of Libnames.object_name

type reset_info = {
  status : reset_status;
  proofs : identifier list;
  cur_prf : (identifier * int) option;
  loc_ast : Util.loc * Vernacexpr.vernac_expr;
}

let com_stk = Stack.create ()

let parsable_of_string s =
  Pcoq.Gram.parsable (Stream.of_string s)

let reset_initial coqtop =
  prerr_endline "Reset initial called"; flush stderr;
  Stack.clear com_stk;
  Vernacentries.abort_refine Lib.reset_initial ()

let compute_reset_info loc_ast = 
  let status,cur_prf = match snd loc_ast with
    | com when is_vernac_tactic_command com ->
        NoReset,Some (Pfedit.get_current_proof_name (),Pfedit.current_proof_depth ())
    | com when is_vernac_state_preserving_command com -> NoReset,None
    | com when is_vernac_proof_ending_command com -> ResetToNextMark,None
    | VernacEndSegment _ -> NoReset,None
    | _ ->
        (match Lib.has_top_frozen_state () with
           | Some sp -> 
               prerr_endline ("On top of state "^Libnames.string_of_path (fst sp));
               ResetAtMark sp,None
           | None -> prerr_endline "No top state"; (NoReset,None))
  in
  { status = status;
    proofs = Pfedit.get_all_proof_names ();
    cur_prf = cur_prf;
    loc_ast = loc_ast; 
  }

let eval_expr cmd_stk loc_ast =
  let rewind_info = compute_reset_info loc_ast in
  Vernac.eval_expr loc_ast;
  Stack.push rewind_info cmd_stk;
  Stack.length cmd_stk

let interp coqtop verbosely s =
  prerr_endline "Starting interp...";
  prerr_endline s;
  let pa = parsable_of_string s in
  try
    let (loc,vernac) = Vernac.parse_sentence (pa,None) in
  (* Temporary hack to make coqide.byte work (WTF???) - now with less screen
  * pollution *)
    Pervasives.prerr_string " \r"; Pervasives.flush stderr;
    if is_vernac_debug_command vernac then
      user_error_loc loc (str "Debug mode not available within CoqIDE");
    if is_vernac_navigation_command vernac then
      user_error_loc loc (str "Use CoqIDE navigation instead");
    if is_vernac_known_option_command vernac then
      user_error_loc loc (str "Use CoqIDE display menu instead");
    if is_vernac_query_command vernac then
      flash_info
        "Warning: query commands should not be inserted in scripts";
    if not (is_vernac_goal_printing_command vernac) then
      (* Verbose if in small step forward and not a tactic *)
      Flags.make_silent (not verbosely);
    let stack_depth = eval_expr com_stk (loc,vernac) in
    Flags.make_silent true;
    prerr_endline ("...Done with interp of : "^s);
    stack_depth
  with Vernac.End_of_input -> assert false

let rewind coqtop count =
  let undo_ops = Hashtbl.create 31 in
  let current_proofs = Pfedit.get_all_proof_names () in
  let rec do_rewind count reset_op prev_proofs curprf =
    if (count <= 0) && (reset_op <> ResetToNextMark) &&
       (Util.list_subset prev_proofs current_proofs) then
      (* We backtracked at least what we wanted to, we have no proof to reopen,
       * and we don't need to find a reset mark *)
      begin
        Hashtbl.iter
          (fun id depth ->
             if List.mem id prev_proofs then begin
               Pfedit.suspend_proof ();
	       Pfedit.resume_proof (Util.dummy_loc,id);
               Pfedit.undo_todepth depth
             end)
          undo_ops;
        prerr_endline "OK for undos";
        Option.iter (fun id -> if List.mem id prev_proofs then
                       Pfedit.suspend_proof ();
		       Pfedit.resume_proof (Util.dummy_loc,id)) curprf;
        prerr_endline "OK for focusing";
        List.iter
          (fun id -> Pfedit.delete_proof (Util.dummy_loc,id))
          (Util.list_subtract current_proofs prev_proofs);
        prerr_endline "OK for aborts";
        (match reset_op with
          | NoReset -> prerr_endline "No Reset"
          | ResetAtMark m -> (prerr_endline ("Reset at "^(Libnames.string_of_path (fst m))); Lib.reset_to_state m)
          | ResetToNextMark -> assert false);
        prerr_endline "OK for reset"
      end
    else
      begin
        prerr_endline "pop";
        let coq = Stack.pop com_stk in
        let curprf =
          Option.map
            (fun (curprf,depth) ->
               (if Hashtbl.mem undo_ops curprf then Hashtbl.replace else Hashtbl.add)
                 undo_ops curprf depth;
               curprf)
            coq.cur_prf in
        do_rewind (pred count)
          (if coq.status <> NoReset then coq.status else reset_op) coq.proofs curprf;
        if count <= 0 then begin
          (* we had to backtrack further to find a suitable anchor point,
           * replaying *)
          prerr_endline "push";
          ignore (eval_expr com_stk coq.loc_ast);
        end
      end
  in
  do_rewind count NoReset current_proofs None;
  Stack.length com_stk


module PrintOpt =
struct
  type t = string list
  let implicit = ["Implicit"]
  let coercions = ["Coercions"]
  let raw_matching = ["Matching";"Synth"]
  let notations = ["Notations"]
  let all_basic = ["All"]
  let existential = ["Existential Instances"]
  let universes = ["Universes"]

  let state_hack = Hashtbl.create 11
  let _ = List.iter (fun opt -> Hashtbl.add state_hack opt false)
            [ implicit; coercions; raw_matching; notations; all_basic; existential; universes ]

  let set coqtop opt value =
    Hashtbl.replace state_hack opt value;
    List.iter
      (fun cmd -> 
         let str = (if value then "Set" else "Unset") ^ " Printing " ^ cmd ^ "." in
         Vernac.eval_expr (Vernac.parse_sentence (parsable_of_string str,None)))
      opt

  let enforce_hack () = Hashtbl.iter (set ()) state_hack 
end

(*
let forbid_vernac blacklist (loc,vernac) =
  List.map (fun (test,err) -> if test vernac then err loc
 *)

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
    | Vernacexpr.Drop ->  str "Drop is not allowed by coqide!",None
    | Vernacexpr.Quit -> str "Quit is not allowed by coqide! Use menus.",None
    | _ ->
	(try Cerrors.explain_exn exc with e ->
	   str "Failed to explain error. This is an internal Coq error. Please report.\n"
	   ++ str (Printexc.to_string  e)),
	(if is_pervasive_exn exc then None else loc)

let process_exn e = let s,loc= print_toplevel_error e in (msgnl s,loc)

type  tried_tactic =
  | Interrupted
  | Success of int (* nb of goals after *)
  | Failed

let string_of_ppcmds c =
  Pp.msg_with Format.str_formatter c;
  Format.flush_str_formatter ()

type 'a menu = 'a * (string * string) list

type goals =
  | Message of string
  | Goals of ((string menu) list * string menu) list

let hyp_next_tac sigma env (id,_,ast) =
  let id_s = Names.string_of_id id in
  let type_s = string_of_ppcmds (pr_ltype_env env ast) in
  [
    ("clear "^id_s),("clear "^id_s^".\n");
    ("apply "^id_s),("apply "^id_s^".\n");
    ("exact "^id_s),("exact "^id_s^".\n");
    ("generalize "^id_s),("generalize "^id_s^".\n");
    ("absurd <"^id_s^">"),("absurd "^type_s^".\n")
  ] @ (if Hipattern.is_equality_type ast then [
    ("discriminate "^id_s),("discriminate "^id_s^".\n");
    ("injection "^id_s),("injection "^id_s^".\n")
  ] else []) @ (if Hipattern.is_equality_type (snd (Reductionops.splay_prod env sigma ast)) then [
    ("rewrite "^id_s),("rewrite "^id_s^".\n");
    ("rewrite <- "^id_s),("rewrite <- "^id_s^".\n")
  ] else []) @ [
    ("elim "^id_s), ("elim "^id_s^".\n");
    ("inversion "^id_s), ("inversion "^id_s^".\n");
    ("inversion clear "^id_s), ("inversion_clear "^id_s^".\n")
  ]

let concl_next_tac sigma concl =
  let expand s = (s,s^".\n") in
  List.map expand ([
    "intro";
    "intros";
    "intuition"
  ] @ (if Hipattern.is_equality_type (Goal.V82.concl sigma concl) then [
    "reflexivity";
    "discriminate";
    "symmetry"
  ] else []) @ [
    "assumption";
    "omega";
    "ring";
    "auto";
    "eauto";
    "tauto";
    "trivial";
    "decide equality";
    "simpl";
    "subst";
    "red";
    "split";
    "left";
    "right"
  ])

let goals coqtop =
  PrintOpt.enforce_hack ();
  let pfts = Pfedit.get_pftreestate () in
  let { it=all_goals ; sigma=sigma } = Proof.V82.subgoals pfts in
  if all_goals = [] then
    begin
      Message (
        let exl = Evarutil.non_instantiated sigma in
        if exl = [] then "Proof Completed.\n" else
          ("No more subgoals but non-instantiated existential variables:\n"^
             string_of_ppcmds (pr_evars_int 1 exl)))
    end
  else
    begin
      let process_goal g =
        let env = Goal.V82.env sigma g in
        let ccl =
          string_of_ppcmds (pr_ltype_env_at_top env (Goal.V82.concl sigma g)) in
        let process_hyp h_env d acc =
          (string_of_ppcmds (pr_var_decl h_env d), hyp_next_tac sigma h_env d)::acc in
        let hyps =
          List.rev (Environ.fold_named_context process_hyp env ~init:[]) in
        (hyps,(ccl,concl_next_tac sigma g))
      in
      Goals (List.map process_goal all_goals)
    end


let id_of_name = function
  | Names.Anonymous -> id_of_string "x"
  | Names.Name x -> x

let make_cases coqtop s =
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
		   let n' = next_ident_away_in_goal
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

let current_status coqtop =
  let path = msg (Libnames.pr_dirpath (Lib.cwd ())) in
  let path = if path = "Top" then "Ready" else "Ready in " ^ String.sub path 4 (String.length path - 4) in
  try
    path ^ ", proving " ^ (Names.string_of_id (Pfedit.get_current_proof_name ()))
  with _ -> path

