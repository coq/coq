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
open Errors
open Util
open Pp
open Printer
open Namegen

(** Ide_slave : an implementation of [Interface], i.e. mainly an interp
    function and a rewind function. This specialized loop is triggered
    when the -ideslave option is passed to Coqtop. Currently CoqIDE is
    the only one using this mode, but we try here to be as generic as
    possible, so this may change in the future... *)

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

let is_known_option cmd = match cmd with
  | VernacSetOption (_,o,BoolValue true)
  | VernacUnsetOption (_,o) -> coqide_known_option o
  | _ -> false

let is_debug cmd = match cmd with
  | VernacSetOption (_,["Ltac";"Debug"], _) -> true
  | _ -> false

let is_query cmd = match cmd with
  | VernacChdir None
  | VernacMemOption _
  | VernacPrintOption _
  | VernacCheckMayEval _
  | VernacGlobalCheck _
  | VernacPrint _
  | VernacSearch _
  | VernacLocate _ -> true
  | _ -> false

let is_undo cmd = match cmd with
  | VernacUndo _ | VernacUndoTo _ -> true
  | _ -> false

(** Check whether a command is forbidden by CoqIDE *)

let coqide_cmd_checks (loc,ast) =
  let user_error s = Errors.user_err_loc (loc, "CoqIde", str s) in
  if is_debug ast then
    user_error "Debug mode not available within CoqIDE";
  if is_known_option ast then
    user_error "Use CoqIDE display menu instead";
  if is_navigation_vernac ast then
    user_error "Use CoqIDE navigation instead";
  if is_undo ast then
    msgerrnl (str "Warning: rather use CoqIDE navigation instead");
  if is_query ast then
    msgerrnl (str "Warning: query commands should not be inserted in scripts")

(** Interpretation (cf. [Ide_intf.interp]) *)

let interp (raw,verbosely,s) =
  let pa = Pcoq.Gram.parsable (Stream.of_string s) in
  let loc_ast = Vernac.parse_sentence (pa,None) in
  if not raw then coqide_cmd_checks loc_ast;
  Flags.make_silent (not verbosely);
  Vernac.eval_expr ~preserving:raw loc_ast;
  Flags.make_silent true;
  read_stdout ()

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
    string_of_ppcmds (pr_goal_concl_style_env env norm_constr) in
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
    let pfts = Proof_global.give_me_the_proof () in
    let { Evd.it = all_goals ; sigma = sigma } = Proof.V82.subgoals pfts in
    let fg = List.map (process_goal sigma) all_goals in
    let { Evd.it = bgoals ; sigma = sigma } = Proof.V82.background_subgoals pfts in
    let bg = List.map (process_goal sigma) bgoals in
    Some { Interface.fg_goals = fg; Interface.bg_goals = bg; }
  with Proof_global.NoCurrentProof -> None

let evars () =
  try
    let pfts = Proof_global.give_me_the_proof () in
    let { Evd.it = all_goals ; sigma = sigma } = Proof.V82.subgoals pfts in
    let exl = Evarutil.non_instantiated sigma in
    let map_evar ev = { Interface.evar_info = string_of_ppcmds (pr_evar ev); } in
    let el = List.map map_evar exl in
    Some el
  with Proof_global.NoCurrentProof -> None

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
  Library.is_in_load_paths (CUnix.physical_path_of_string dir)

let status () =
  (** We remove the initial part of the current [dir_path]
      (usually Top in an interactive session, cf "coqtop -top"),
      and display the other parts (opened sections and modules) *)
  let path =
    let l = Names.repr_dirpath (Lib.cwd ()) in
    List.rev_map Names.string_of_id l
  in
  let proof =
    try Some (Names.string_of_id (Proof_global.get_current_proof_name ()))
    with _ -> None
  in
  let allproofs =
    let l = Proof_global.get_all_proof_names () in
    List.map Names.string_of_id l
  in
  {
    Interface.status_path = path;
    Interface.status_proofname = proof;
    Interface.status_allproofs = allproofs;
    Interface.status_statenum = Lib.current_command_label ();
    Interface.status_proofnum = Pfedit.current_proof_depth ();
  }

let get_options () =
  let table = Goptions.get_tables () in
  let fold key state accu = (key, state) :: accu in
  Goptions.OptionMap.fold fold table []

let set_options options =
  let iter (name, value) = match value with
  | BoolValue b -> Goptions.set_bool_option_value name b
  | IntValue i -> Goptions.set_int_option_value name i
  | StringValue s -> Goptions.set_string_option_value name s
  in
  List.iter iter options

(** Grouping all call handlers together + error handling *)

let eval_call c =
  let rec handle_exn e =
    catch_break := false;
    let pr_exn e = (read_stdout ())^("\n"^(string_of_ppcmds (Errors.print e))) in
    match e with
      | Vernacexpr.Drop -> None, "Drop is not allowed by coqide!"
      | Vernacexpr.Quit -> None, "Quit is not allowed by coqide!"
      | Vernac.DuringCommandInterp (_,inner) -> handle_exn inner
      | Error_in_file (_,_,inner) -> None, pr_exn inner
      | Loc.Exc_located (loc, inner) when loc = dummy_loc -> None, pr_exn inner
      | Loc.Exc_located (loc, inner) -> Some (Pp.unloc loc), pr_exn inner
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
    Interface.rewind = interruptible Backtrack.back;
    Interface.goals = interruptible goals;
    Interface.evars = interruptible evars;
    Interface.hints = interruptible hints;
    Interface.status = interruptible status;
    Interface.inloadpath = interruptible inloadpath;
    Interface.get_options = interruptible get_options;
    Interface.set_options = interruptible set_options;
    Interface.mkcases = interruptible Vernacentries.make_cases;
    Interface.handle_exn = handle_exn; }
  in
  (* If the messages of last command are still there, we remove them *)
  ignore (read_stdout ());
  Serialize.abstract_eval_call handler c


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
  Serialize.of_value (fun _ -> assert false) (Interface.Fail (None, err))

let loop () =
  let p = Xml_parser.make () in
  let () = Xml_parser.check_eof p false in
  init_signal_handler ();
  catch_break := false;
  (* We'll handle goal fetching and display in our own way *)
  Vernacentries.enable_goal_printing := false;
  Vernacentries.qed_display_script := false;
  try
    while true do
      let xml_answer =
        try
          let xml_query = Xml_parser.parse p (Xml_parser.SChannel stdin) in
          let q = Serialize.to_call xml_query in
          let () = pr_debug ("<-- " ^ Serialize.pr_call q) in
          let r = eval_call q in
          let () = pr_debug ("--> " ^ Serialize.pr_full_value q r) in
          Serialize.of_answer q r
        with
        | Xml_parser.Error (err, loc) ->
          let msg = "Syntax error in query: " ^ Xml_parser.error_msg err in
          fail msg
        | Serialize.Marshal_error ->
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
