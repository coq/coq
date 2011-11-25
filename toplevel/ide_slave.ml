(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Vernacexpr
open Names
open Compat
open Util
open Pp
open Printer
open Namegen

(** Ide_slave : an implementation of [Interface], i.e. mainly an interp
    function and a rewind function. This specialized loop is triggered
    when the -ideslave option is passed to Coqtop. Currently CoqIDE is
    the only one using this mode, but we try here to be as generic as
    possible, so this may change in the future... *)


(** Comment the next line for displaying some more debug messages *)

let prerr_endline _ = ()


(** Signal handling: we postpone ^C during input and output phases,
    but make it directly raise a Sys.Break during evaluation of the request. *)

let catch_break = ref false

let init_signal_handler () =
  let f _ = if !catch_break then raise Sys.Break else Util.interrupt := true in
  Sys.set_signal Sys.sigint (Sys.Signal_handle f)


(** Redirection of standard output to a printable buffer *)

let orig_stdout = ref stdout

let init_stdout,read_stdout =
  let out_buff = Buffer.create 100 in
  let out_ft = Format.formatter_of_buffer out_buff in
  let deep_out_ft = Format.formatter_of_buffer out_buff in
  let _ = Pp_control.set_gp deep_out_ft Pp_control.deep_gp in
  (fun () ->
     flush_all ();
     orig_stdout := Unix.out_channel_of_descr (Unix.dup Unix.stdout);
     Unix.dup2 Unix.stderr Unix.stdout;
     Pp_control.std_ft := out_ft;
     Pp_control.err_ft := out_ft;
     Pp_control.deep_ft := deep_out_ft;
     set_binary_mode_out !orig_stdout true;
     set_binary_mode_in stdin true;
  ),
  (fun () -> Format.pp_print_flush out_ft ();
             let r = Buffer.contents out_buff in
             Buffer.clear out_buff; r)


(** Categories of commands *)

let coqide_known_option table = List.mem table [
  ["Printing";"Implicit"];
  ["Printing";"Coercions"];
  ["Printing";"Matching"];
  ["Printing";"Synth"];
  ["Printing";"Notations"];
  ["Printing";"All"];
  ["Printing";"Records"];
  ["Printing";"Existential";"Instances"];
  ["Printing";"Universes"]]

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
  | VernacDeclareInstances _ -> []
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
  | VernacChdir o ->
    (* TODO: [Chdir d] is currently not undo-able (not stored in coq state).
       But if we register [Chdir] in the state, loading [initial.coq] will
       wrongly cd to the compile-time directory at each coqtop launch. *)
    if o = None then [QueryCommand] else []

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
  | VernacRemoveHints _ -> []
  | VernacHints _ -> []
  | VernacSyntacticDefinition _ -> []
  | VernacDeclareImplicits _ -> []
  | VernacArguments _ -> [] 
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

  | VernacAbort _ -> []
  | VernacAbortAll -> [NavigationCommand]
  | VernacRestart -> [NavigationCommand]
  | VernacSuspend -> [NavigationCommand]
  | VernacResume _ -> [NavigationCommand]
  | VernacUndo _ -> [NavigationCommand]
  | VernacUndoTo _ -> [NavigationCommand]
  | VernacBacktrack _ -> [NavigationCommand]

  | VernacFocus _ -> [SolveCommand]
  | VernacUnfocus -> [SolveCommand]
  | VernacShow _ -> [OtherStatePreservingCommand]
  | VernacCheckGuard -> [OtherStatePreservingCommand]
  | VernacProof (Tacexpr.TacId []) -> [OtherStatePreservingCommand]
  | VernacProof _ -> []

  | VernacProofMode _ -> []
  | VernacSubproof _ -> [SolveCommand]
  | VernacEndSubproof -> [SolveCommand]

  (* Toplevel control *)
  | VernacToplevelControl _ -> []

  (* Extensions *)
  | VernacExtend ("Subtac_Obligations", _) -> [GoalStartingCommand]
  | VernacExtend _ -> []

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


(** Command history stack

    We maintain a stack of the past states of the system. Each
    successfully interpreted command adds a [reset_info] element
    to this stack, storing what were the (label / open proofs /
    current proof depth) just _before_ the interpretation of this
    command. A label is just an integer (cf. BackTo and Bactrack
    vernac commands).
*)

type reset_info = { label : int; proofs : identifier list; depth : int }

let com_stk = Stack.create ()

let compute_reset_info () =
  { label = Lib.current_command_label ();
    proofs = Pfedit.get_all_proof_names ();
    depth = max 0 (Pfedit.current_proof_depth ()) }


(** Interpretation (cf. [Ide_intf.interp]) *)

(** Check whether a command is forbidden by CoqIDE *)

let coqide_cmd_checks (loc,ast) =
  let user_error s =
    raise (Loc.Exc_located (loc, Util.UserError ("CoqIde", str s)))
  in
  if is_vernac_debug_command ast then
    user_error "Debug mode not available within CoqIDE";
  if is_vernac_navigation_command ast then
    user_error "Use CoqIDE navigation instead";
  if is_vernac_known_option_command ast then
    user_error "Use CoqIDE display menu instead";
  if is_vernac_query_command ast then
    msgerrnl (str "Warning: query commands should not be inserted in scripts")

let raw_eval_expr = Vernac.eval_expr

let eval_expr loc_ast =
  let rewind_info = compute_reset_info () in
  raw_eval_expr loc_ast;
  Stack.push rewind_info com_stk

let interp (raw,verbosely,s) =
  if not raw then (prerr_endline "Starting interp..."; prerr_endline s);
  let pa = Pcoq.Gram.parsable (Stream.of_string s) in
  let loc_ast = Vernac.parse_sentence (pa,None) in
  if not raw then coqide_cmd_checks loc_ast;
  (* We run tactics silently, since we will query the goal state later.
     Otherwise, we honor the IDE verbosity flag. *)
  Flags.make_silent
    (is_vernac_goal_printing_command (snd loc_ast) || not verbosely);
  if raw then raw_eval_expr loc_ast else eval_expr loc_ast;
  Flags.make_silent true;
  if not raw then prerr_endline ("...Done with interp of : "^s);
  read_stdout ()


(** Backtracking (cf. [Ide_intf.rewind]).
    We now rely on the [Backtrack] command just as ProofGeneral. *)

let rewind count =
  if count = 0 then 0
  else
    let current_proofs = Pfedit.get_all_proof_names ()
    in
    (* 1) First, let's pop the history stack exactly [count] times.
       NB: Normally, the IDE will not rewind by more than the numbers
       of already interpreted commands, hence no risk of [Stack.Empty].
    *)
    let initial_target =
      for i = 1 to count - 1 do ignore (Stack.pop com_stk) done;
      Stack.pop com_stk
    in
    (* 2) Backtrack by enough additional steps to avoid re-opening proofs.
       Typically, when a Qed has been crossed, we backtrack to the proof start.
       NB: We cannot reach the empty stack, since the oldest [reset_info]
       in the history cannot have opened proofs.
    *)
    let already_opened p = List.mem p current_proofs in
    let rec extra_back n target =
      if List.for_all already_opened target.proofs then n,target
      else extra_back (n+1) (Stack.pop com_stk)
    in
    let extra_count, target = extra_back 0 initial_target
    in
    (* 3) Now that [target.proofs] is a subset of the opened proofs before
       the rewind, we simply abort the extra proofs (if any).
       NB: It is critical here that proofs are nested in a regular way
       (i.e. no Resume or Suspend, as enforced above). This way, we can simply
       count the extra proofs to abort instead of taking care of their names.
    *)
    let naborts = List.length current_proofs - List.length target.proofs
    in
    (* 4) We are now ready to call [Backtrack] *)
    prerr_endline ("Rewind to state "^string_of_int target.label^
		   ", proof depth "^string_of_int target.depth^
		   ", num of aborts "^string_of_int naborts);
    Vernacentries.vernac_backtrack target.label target.depth naborts;
    Lib.mark_end_of_command (); (* We've short-circuited Vernac.eval_expr *)
    extra_count


(** Goal display *)

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

let process_goal sigma g =
  let env = Goal.V82.env sigma g in
  let ccl =
    let norm_constr = Reductionops.nf_evar sigma (Goal.V82.concl sigma g) in
    string_of_ppcmds (pr_ltype_env_at_top env norm_constr) in
  let process_hyp h_env d acc =
    let d = Term.map_named_declaration (Reductionops.nf_evar sigma) d in
    (string_of_ppcmds (pr_var_decl h_env d)) :: acc in
(*           (string_of_ppcmds (pr_var_decl h_env d), hyp_next_tac sigma h_env d)::acc in *)
  let hyps =
    List.rev (Environ.fold_named_context process_hyp env ~init: []) in
  { Interface.goal_hyp = hyps; Interface.goal_ccl = ccl }
(*         hyps,(ccl,concl_next_tac sigma g)) *)

let goals () =
  try
    let pfts =
      Proof_global.give_me_the_proof ()
    in
  let { Evd.it=all_goals ; sigma=sigma } = Proof.V82.subgoals pfts in
  if all_goals = [] then
    begin
      let { Evd.it = bgoals ; sigma = sigma } = Proof.V82.background_subgoals pfts in
      if bgoals = [] then
        let exl = Evarutil.non_instantiated sigma in
        if exl = [] then Interface.Proof_completed
        else
          let el = List.map (fun evar -> string_of_ppcmds (pr_evar evar)) exl in
          Interface.Uninstantiated_evars el
      else Interface.Unfocused_goals (List.map (process_goal sigma) bgoals)
    end
  else
    Interface.Goals (List.map (process_goal sigma) all_goals)
  with Proof_global.NoCurrentProof -> Interface.No_current_proof

let hints () =
  try
    let pfts = Proof_global.give_me_the_proof () in
    let { Evd.it = all_goals ; sigma = sigma } = Proof.V82.subgoals pfts in
    match all_goals with
    | [] -> None
    | g :: _ ->
      let env = Goal.V82.env sigma g in
      let hint_goal = concl_next_tac sigma g in
      let get_hint_hyp env d accu = hyp_next_tac sigma env d :: accu in
      let hint_hyps = List.rev (Environ.fold_named_context get_hint_hyp env ~init: []) in
      Some (hint_hyps, hint_goal)
  with Proof_global.NoCurrentProof -> None

(** Other API calls *)

let inloadpath dir =
  Library.is_in_load_paths (System.physical_path_of_string dir)

let status () =
  (** We remove the initial part of the current [dir_path]
      (usually Top in an interactive session, cf "coqtop -top"),
      and display the other parts (opened sections and modules) *)
  let path =
    let l = Names.repr_dirpath (Lib.cwd ()) in
    let l = snd (Util.list_sep_last l) in
    if l = [] then None
    else Some (Names.string_of_dirpath (Names.make_dirpath l))
  in
  let proof =
    try
      Some (Names.string_of_id (Pfedit.get_current_proof_name ()))
    with _ -> None
  in
  { Interface.status_path = path; Interface.status_proofname = proof }

(** Grouping all call handlers together + error handling *)

let eval_call c =
  let rec handle_exn e =
    catch_break := false;
    let pr_exn e = string_of_ppcmds (Errors.print e) in
    match e with
      | Vernacexpr.Drop -> None, "Drop is not allowed by coqide!"
      | Vernacexpr.Quit -> None, "Quit is not allowed by coqide!"
      | Vernac.DuringCommandInterp (_,inner) -> handle_exn inner
      | Error_in_file (_,_,inner) -> None, pr_exn inner
      | Loc.Exc_located (loc, inner) when loc = dummy_loc -> None, pr_exn inner
      | Loc.Exc_located (loc, inner) -> Some (Util.unloc loc), pr_exn inner
      | e -> None, pr_exn e
  in
  let interruptible f x =
    catch_break := true;
    Util.check_for_interrupt ();
    let r = f x in
    catch_break := false;
    r
  in
  let handler = {
    Interface.interp = interruptible interp;
    Interface.rewind = interruptible rewind;
    Interface.goals = interruptible goals;
    Interface.hints = interruptible hints;
    Interface.status = interruptible status;
    Interface.inloadpath = interruptible inloadpath;
    Interface.mkcases = interruptible Vernacentries.make_cases;
    Interface.handle_exn = handle_exn; }
  in
  (* If the messages of last command are still there, we remove them *)
  ignore (read_stdout ());
  Ide_intf.abstract_eval_call handler c


(** The main loop *)

(** Exceptions during eval_call should be converted into [Interface.Fail]
    messages by [handle_exn] above. Otherwise, we die badly, after having
    tried to send a last message to the ide: trying to recover from errors
    with the current protocol would most probably bring desynchronisation
    between coqtop and ide. With marshalling, reading an answer to
    a different request could hang the ide... *)

let pr_debug s =
  if !Flags.debug then Printf.eprintf "[pid %d] %s\n%!" (Unix.getpid ()) s

let fail err =
  Ide_intf.of_value (fun _ -> assert false) (Interface.Fail (None, err))

let loop () =
  let p = Xml_parser.make () in
  let () = Xml_parser.check_eof p false in
  init_signal_handler ();
  catch_break := false;
  (* ensure we have a command separator object (DOT) so that the first
     command can be reseted. *)
  Lib.mark_end_of_command();
  try
    while true do
      let xml_answer =
        try
          let xml_query = Xml_parser.parse p (Xml_parser.SChannel stdin) in
          let q = Ide_intf.to_call xml_query in
          let () = pr_debug ("<-- " ^ Ide_intf.pr_call q) in
          let r = eval_call q in
          let () = pr_debug ("--> " ^ Ide_intf.pr_full_value q r) in
          Ide_intf.of_answer q r
        with
        | Xml_parser.Error (err, loc) ->
          let msg = "Syntax error in query: " ^ Xml_parser.error_msg err in
          fail msg
        | Ide_intf.Marshal_error ->
          fail "Incorrect query."
      in
      Xml_utils.print_xml !orig_stdout xml_answer;
      flush !orig_stdout
    done
  with e ->
    let msg = Printexc.to_string e in
    let r = "Fatal exception in coqtop:\n" ^ msg in
    pr_debug ("==> " ^ r);
    (try
      Xml_utils.print_xml !orig_stdout (fail r);
      flush !orig_stdout
    with _ -> ());
    exit 1
