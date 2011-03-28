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

let prerr_endline _ = ()

let coqide_known_option table = List.mem table [
  ["Printing";"Implicit"];
  ["Printing";"Coercions"];
  ["Printing";"Matching"];
  ["Printing";"Synth"];
  ["Printing";"Notations"];
  ["Printing";"All"];
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
  | VernacRemoveHints _ -> []
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
  | VernacShow _ -> [OtherStatePreservingCommand]
  | VernacCheckGuard -> [OtherStatePreservingCommand]
  | VernacProof (Tacexpr.TacId []) -> [OtherStatePreservingCommand]
  | VernacProof _ -> []

  | VernacProofMode _ -> []
  | VernacSubproof _ -> []
  | VernacEndSubproof -> []

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

let reinit () =
  Vernacentries.abort_refine Lib.reset_initial ();
  Stack.clear com_stk

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

let parsable_of_string s =
  Pcoq.Gram.parsable (Stream.of_string s)

let eval_expr loc_ast =
  let rewind_info = compute_reset_info loc_ast in
  Vernac.eval_expr loc_ast;
  Stack.push rewind_info com_stk;
  Stack.length com_stk

let raw_interp s =
  Vernac.eval_expr (Vernac.parse_sentence (parsable_of_string s,None))

let user_error_loc l s =
    raise (Loc.Exc_located (l, Util.UserError ("CoqIde", s)))

let interp verbosely s =
  prerr_endline "Starting interp...";
  prerr_endline s;
  let pa = parsable_of_string s in
  try
    let (loc,vernac) = Vernac.parse_sentence (pa,None) in
    (* Temporary hack to make coqide.byte work (WTF???) - now with
     * less screen
     *   * pollution *)
    Pervasives.prerr_string " \r"; Pervasives.flush stderr;
    if is_vernac_debug_command vernac then
      user_error_loc loc (str "Debug mode not available within CoqIDE");
    if is_vernac_navigation_command vernac then
      user_error_loc loc (str "Use CoqIDE navigation instead");
    if is_vernac_known_option_command vernac then
      user_error_loc loc (str "Use CoqIDE display menu instead");
    if is_vernac_query_command vernac then
      msgerrnl (str "Warning: query commands should not be inserted in scripts");
    if not (is_vernac_goal_printing_command vernac) then
      (* Verbose if in small step forward and not a tactic *)
      Flags.make_silent (not verbosely);
    let stack_depth = eval_expr (loc,vernac) in
    Flags.make_silent true;
    prerr_endline ("...Done with interp of : "^s);
    stack_depth
  with Vernac.End_of_input -> assert false

let rewind count =
  let undo_ops = Hashtbl.create 31 in
  let current_proofs = Pfedit.get_all_proof_names () in
  let rec do_rewind count reset_op prev_proofs curprf =
    if (count <= 0) && (reset_op <> ResetToNextMark) &&
       (Util.list_subset prev_proofs current_proofs) then
      (* We backtracked at least what we wanted to, we have no
       * proof to reopen, and we don't need to find a reset mark *)
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
              (* we had to backtrack further to find a suitable
               * anchor point, replaying *)
              prerr_endline "push";
              ignore (eval_expr coq.loc_ast);
            end
          end
  in
  do_rewind count NoReset current_proofs None;
  Stack.length com_stk

let is_in_loadpath dir =
  Library.is_in_load_paths (System.physical_path_of_string dir)

let string_of_ppcmds c =
  Pp.msg_with Format.str_formatter c;
  Format.flush_str_formatter ()

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

let current_goals () =
  try
    let pfts =
      Proof_global.give_me_the_proof ()
    in
  let { Evd.it=all_goals ; sigma=sigma } = Proof.V82.subgoals pfts in
  if all_goals = [] then
    begin
      Ide_intf.Message (string_of_ppcmds (
        let { Evd.it = bgoals ; sigma = sigma } = Proof.V82.background_subgoals pfts in
        match bgoals with
          | [] ->
              let exl = Evarutil.non_instantiated sigma in
              (str (if exl = [] then "Proof Completed." else
                      "No more subgoals but non-instantiated existential variables:") ++
               (fnl ()) ++ (pr_evars_int 1 exl))
          | _ ->
              Util.list_fold_left_i
                (fun i a g ->
                   a ++ (Printer.pr_concl i sigma g) ++ (spc ())) 1
                (str "This subproof is complete, but there are still unfocused goals:" ++ (fnl ()))
                bgoals))
    end
  else
    begin
      let process_goal g =
        let env = Goal.V82.env sigma g in
        let ccl =
          let norm_constr = Reductionops.nf_evar sigma (Goal.V82.concl sigma g) in
          string_of_ppcmds (pr_ltype_env_at_top env norm_constr) in
        let process_hyp h_env d acc =
          let d = Term.map_named_declaration (Reductionops.nf_evar sigma) d in
          (string_of_ppcmds (pr_var_decl h_env d), hyp_next_tac sigma h_env d)::acc in
        let hyps =
          List.rev (Environ.fold_named_context process_hyp env ~init:[]) in
        (hyps,(ccl,concl_next_tac sigma g))
      in
      Ide_intf.Goals (List.map process_goal all_goals)
    end
  with Proof_global.NoCurrentProof ->
    Ide_intf.Message "" (* quick hack to have a clean message screen *)

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

let current_status () =
  (** We remove the initial part of the current [dir_path]
      (usually Top in an interactive session, cf "coqtop -top"),
      and display the other parts (opened sections and modules) *)
  let path =
    let l = Names.repr_dirpath (Lib.cwd ()) in
    let l = snd (Util.list_sep_last l) in
    if l = [] then "" else
      (" in "^Names.string_of_dirpath (Names.make_dirpath l))
  in
  let proof =
    try
      ", proving " ^ (Names.string_of_id (Pfedit.get_current_proof_name ()))
    with _ -> ""
  in
  "Ready"^path^proof

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

let explain_exn e =
  let toploc,exc =
    match e with
      | Loc.Exc_located (loc, inner) ->
	let l = if loc = dummy_loc then None else Some (Util.unloc loc) in
	l,inner
      | Error_in_file (s, _, inner) -> None,inner
      | _ -> None,e
  in
  toploc,(Cerrors.explain_exn exc)

let eval_call c =
  let rec handle_exn = function
    | Vernac.DuringCommandInterp (loc,inner) -> handle_exn inner
    | Vernacexpr.Drop -> None, "Drop is not allowed by coqide!"
    | Vernacexpr.Quit -> None, "Quit is not allowed by coqide!"
    | e ->
      let (l,pp) = explain_exn e in
      l, string_of_ppcmds pp
  in
  let handler = {
    Ide_intf.is_in_loadpath = is_in_loadpath;
    Ide_intf.raw_interp = raw_interp;
    Ide_intf.interp = interp;
    Ide_intf.rewind = rewind;
    Ide_intf.read_stdout = read_stdout;
    Ide_intf.current_goals = current_goals;
    Ide_intf.current_status = current_status;
    Ide_intf.make_cases = make_cases }
  in
  Ide_intf.abstract_eval_call handler handle_exn c

let loop () =
  Sys.catch_break true;
  try
    while true do
      let q = (Marshal.from_channel: in_channel -> 'a Ide_intf.call) stdin in
      let r = eval_call q in
      Marshal.to_channel !orig_stdout r [];
      flush !orig_stdout
    done
  with
    | Vernacexpr.Quit -> exit 0
    | _ -> exit 1
