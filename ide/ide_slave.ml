(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Vernacexpr
open Errors
open Util
open Pp
open Printer

(** Ide_slave : an implementation of [Interface], i.e. mainly an interp
    function and a rewind function. This specialized loop is triggered
    when the -ideslave option is passed to Coqtop. Currently CoqIDE is
    the only one using this mode, but we try here to be as generic as
    possible, so this may change in the future... *)

(** Signal handling: we postpone ^C during input and output phases,
    but make it directly raise a Sys.Break during evaluation of the request. *)

let catch_break = ref false

let init_signal_handler () =
  let f _ = if !catch_break then raise Sys.Break else Control.interrupt := true in
  Sys.set_signal Sys.sigint (Sys.Signal_handle f)


(** Redirection of standard output to a printable buffer *)

let init_stdout, read_stdout =
  let out_buff = Buffer.create 100 in
  let out_ft = Format.formatter_of_buffer out_buff in
  let deep_out_ft = Format.formatter_of_buffer out_buff in
  let _ = Pp_control.set_gp deep_out_ft Pp_control.deep_gp in
  (fun () ->
     flush_all ();
     Pp_control.std_ft := out_ft;
     Pp_control.err_ft := out_ft;
     Pp_control.deep_ft := deep_out_ft;
  ),
  (fun () -> Format.pp_print_flush out_ft ();
             let r = Buffer.contents out_buff in
             Buffer.clear out_buff; r)

let pr_with_pid s = Printf.eprintf "[pid %d] %s\n%!" (Unix.getpid ()) s

let pr_debug s =
  if !Flags.debug then pr_with_pid s
let pr_debug_call q =
  if !Flags.debug then pr_with_pid ("<-- " ^ Xmlprotocol.pr_call q)
let pr_debug_answer q r =
  if !Flags.debug then pr_with_pid ("--> " ^ Xmlprotocol.pr_full_value q r)

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
  | VernacSetOption (o,BoolValue true)
  | VernacUnsetOption o -> coqide_known_option o
  | _ -> false

let is_debug cmd = match cmd with
  | VernacSetOption (["Ltac";"Debug"], _) -> true
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
    msg_warning (strbrk"This will not work. Use CoqIDE display menu instead");
  if Vernac.is_navigation_vernac ast || is_undo ast then
    msg_warning (strbrk "Rather use CoqIDE navigation instead");
  if is_query ast then
    msg_warning (strbrk "Query commands should not be inserted in scripts")

(** Interpretation (cf. [Ide_intf.interp]) *)

let add ((s,eid),(sid,verbose)) =
  let newid, rc = Stm.add ~ontop:sid verbose ~check:coqide_cmd_checks eid s in
  let rc = match rc with `NewTip -> CSig.Inl () | `Unfocus id -> CSig.Inr id in
  newid, (rc, read_stdout ())

let edit_at id =
  match Stm.edit_at id with
  | `NewTip -> CSig.Inl ()
  | `Focus { Stm.start; stop; tip} -> CSig.Inr (start, (stop, tip))

let query (s,id) = Stm.query ~at:id s; read_stdout ()

let annotate phrase =
  let (loc, ast) =
    let pa = Pcoq.Gram.parsable (Stream.of_string phrase) in
    Vernac.parse_sentence (pa,None)
  in
  let (_, _, xml) =
    Richprinter.richpp_vernac ast
  in
  xml

(** Goal display *)

let hyp_next_tac sigma env (id,_,ast) =
  let id_s = Names.Id.to_string id in
  let type_s = string_of_ppcmds (pr_ltype_env env sigma ast) in
  [
    ("clear "^id_s),("clear "^id_s^".");
    ("apply "^id_s),("apply "^id_s^".");
    ("exact "^id_s),("exact "^id_s^".");
    ("generalize "^id_s),("generalize "^id_s^".");
    ("absurd <"^id_s^">"),("absurd "^type_s^".")
  ] @ [
    ("discriminate "^id_s),("discriminate "^id_s^".");
    ("injection "^id_s),("injection "^id_s^".")
  ] @ [
    ("rewrite "^id_s),("rewrite "^id_s^".");
    ("rewrite <- "^id_s),("rewrite <- "^id_s^".")
  ] @ [
    ("elim "^id_s), ("elim "^id_s^".");
    ("inversion "^id_s), ("inversion "^id_s^".");
    ("inversion clear "^id_s), ("inversion_clear "^id_s^".")
  ]

let concl_next_tac sigma concl =
  let expand s = (s,s^".") in
  List.map expand ([
    "intro";
    "intros";
    "intuition"
  ] @ [
    "reflexivity";
    "discriminate";
    "symmetry"
  ] @ [
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
  let min_env = Environ.reset_context env in
  let id = Goal.uid g in
  let ccl =
    let norm_constr = Reductionops.nf_evar sigma (Goal.V82.concl sigma g) in
    string_of_ppcmds (pr_goal_concl_style_env env sigma norm_constr) in
  let process_hyp d =
    let d = Context.map_named_list_declaration (Reductionops.nf_evar sigma) d in
    (string_of_ppcmds (pr_var_list_decl min_env sigma d)) in
  let hyps =
    List.map process_hyp
      (Termops.compact_named_context_reverse (Environ.named_context env)) in
  { Interface.goal_hyp = hyps; Interface.goal_ccl = ccl; Interface.goal_id = id; }

let export_pre_goals pgs =
  {
    Interface.fg_goals       = pgs.Proof.fg_goals;
    Interface.bg_goals       = pgs.Proof.bg_goals;
    Interface.shelved_goals  = pgs.Proof.shelved_goals;
    Interface.given_up_goals = pgs.Proof.given_up_goals
  }

let goals () =
  Stm.finish ();
  let s = read_stdout () in
  if not (String.is_empty s) then msg_info (str s);
  try
    let pfts = Proof_global.give_me_the_proof () in
    Some (export_pre_goals (Proof.map_structured_proof pfts process_goal))
  with Proof_global.NoCurrentProof -> None

let evars () =
  try
    Stm.finish ();
    let s = read_stdout () in
    if not (String.is_empty s) then msg_info (str s);
    let pfts = Proof_global.give_me_the_proof () in
    let { Evd.it = all_goals ; sigma = sigma } = Proof.V82.subgoals pfts in
    let exl = Evar.Map.bindings (Evarutil.non_instantiated sigma) in
    let map_evar ev = { Interface.evar_info = string_of_ppcmds (pr_evar sigma ev); } in
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

let status force =
  (** We remove the initial part of the current [DirPath.t]
      (usually Top in an interactive session, cf "coqtop -top"),
      and display the other parts (opened sections and modules) *)
  Stm.finish ();
  if force then Stm.join ();
  let s = read_stdout () in
  if not (String.is_empty s) then msg_info (str s);
  let path =
    let l = Names.DirPath.repr (Lib.cwd ()) in
    List.rev_map Names.Id.to_string l
  in
  let proof =
    try Some (Names.Id.to_string (Proof_global.get_current_proof_name ()))
    with Proof_global.NoCurrentProof -> None
  in
  let allproofs =
    let l = Proof_global.get_all_proof_names () in
    List.map Names.Id.to_string l
  in
  {
    Interface.status_path = path;
    Interface.status_proofname = proof;
    Interface.status_allproofs = allproofs;
    Interface.status_proofnum = Stm.current_proof_depth ();
  }

let export_coq_object t = {
  Interface.coq_object_prefix = t.Search.coq_object_prefix;
  Interface.coq_object_qualid = t.Search.coq_object_qualid;
  Interface.coq_object_object = t.Search.coq_object_object
}

let import_search_constraint = function
  | Interface.Name_Pattern s    -> Search.Name_Pattern s
  | Interface.Type_Pattern s    -> Search.Type_Pattern s
  | Interface.SubType_Pattern s -> Search.SubType_Pattern s
  | Interface.In_Module ms      -> Search.In_Module ms
  | Interface.Include_Blacklist -> Search.Include_Blacklist

let search flags =
  List.map export_coq_object (Search.interface_search (
    List.map (fun (c, b) -> (import_search_constraint c, b)) flags)
  )

let export_option_value = function
  | Goptions.BoolValue b   -> Interface.BoolValue b
  | Goptions.IntValue x    -> Interface.IntValue x
  | Goptions.StringValue s -> Interface.StringValue s

let import_option_value = function
  | Interface.BoolValue b   -> Goptions.BoolValue b
  | Interface.IntValue x    -> Goptions.IntValue x
  | Interface.StringValue s -> Goptions.StringValue s

let export_option_state s = {
  Interface.opt_sync  = s.Goptions.opt_sync;
  Interface.opt_depr  = s.Goptions.opt_depr;
  Interface.opt_name  = s.Goptions.opt_name;
  Interface.opt_value = export_option_value s.Goptions.opt_value;
}

let get_options () =
  let table = Goptions.get_tables () in
  let fold key state accu = (key, export_option_state state) :: accu in
  Goptions.OptionMap.fold fold table []

let set_options options =
  let iter (name, value) = match import_option_value value with
  | BoolValue b -> Goptions.set_bool_option_value name b
  | IntValue i -> Goptions.set_int_option_value name i
  | StringValue s -> Goptions.set_string_option_value name s
  in
  List.iter iter options

let about () = {
  Interface.coqtop_version = Coq_config.version;
  Interface.protocol_version = Xmlprotocol.protocol_version;
  Interface.release_date = Coq_config.date;
  Interface.compile_date = Coq_config.compile_date;
}

let handle_exn (e, info) =
  let dummy = Stateid.dummy in
  let loc_of e = match Loc.get_loc e with
    | Some loc when not (Loc.is_ghost loc) -> Some (Loc.unloc loc)
    | _ -> None in
  let mk_msg e = read_stdout ()^"\n"^string_of_ppcmds (Errors.print e) in
  match e with
  | Errors.Drop -> dummy, None, "Drop is not allowed by coqide!"
  | Errors.Quit -> dummy, None, "Quit is not allowed by coqide!"
  | e ->
      match Stateid.get info with
      | Some (valid, _) -> valid, loc_of info, mk_msg e
      | None -> dummy, loc_of info, mk_msg e

let init =
  let initialized = ref false in
  fun file ->
   if !initialized then anomaly (str "Already initialized")
   else begin
     initialized := true;
     match file with
     | None -> Stm.get_current_state ()
     | Some file ->
         if not (Filename.check_suffix file ".v") then
           error "A file with suffix .v is expected.";
         let dir = Filename.dirname file in
         let open Loadpath in let open CUnix in
         let initial_id, _ =
           if not (is_in_load_paths (physical_path_of_string dir)) then
             Stm.add false ~ontop:(Stm.get_current_state ())
               0 (Printf.sprintf "Add LoadPath \"%s\". " dir)
           else Stm.get_current_state (), `NewTip in
         Stm.set_compilation_hints file;
         initial_id
   end

(* Retrocompatibility stuff *)
let interp ((_raw, verbose), s) =
  let vernac_parse s =
    let pa = Pcoq.Gram.parsable (Stream.of_string s) in
    Flags.with_option Flags.we_are_parsing (fun () ->
      match Pcoq.Gram.entry_parse Pcoq.main_entry pa with
      | None -> raise (Invalid_argument "vernac_parse")
      | Some ast -> ast)
    () in
  Stm.interp verbose (vernac_parse s);
  Stm.get_current_state (), CSig.Inl (read_stdout ())

(** When receiving the Quit call, we don't directly do an [exit 0],
    but rather set this reference, in order to send a final answer
    before exiting. *)

let quit = ref false

(** Grouping all call handlers together + error handling *)

let eval_call xml_oc log c =
  let interruptible f x =
    catch_break := true;
    Control.check_for_interrupt ();
    let r = f x in
    catch_break := false;
    let out = read_stdout () in
    if not (String.is_empty out) then log (str out);
    r
  in
  let handler = {
    Interface.add = interruptible add;
    Interface.edit_at = interruptible edit_at;
    Interface.query = interruptible query;
    Interface.goals = interruptible goals;
    Interface.evars = interruptible evars;
    Interface.hints = interruptible hints;
    Interface.status = interruptible status;
    Interface.search = interruptible search;
    Interface.get_options = interruptible get_options;
    Interface.set_options = interruptible set_options;
    Interface.mkcases = interruptible Vernacentries.make_cases;
    Interface.quit = (fun () -> quit := true);
    Interface.init = interruptible init;
    Interface.about = interruptible about;
    Interface.interp = interruptible interp;
    Interface.handle_exn = handle_exn;
    Interface.stop_worker = Stm.stop_worker;
    Interface.print_ast = Stm.print_ast;
    Interface.annotate = interruptible annotate;
  } in
  Xmlprotocol.abstract_eval_call handler c

(** Message dispatching.
    Since coqtop -ideslave starts 1 thread per slave, and each
    thread forwards feedback messages from the slave to the GUI on the same
    xml channel, we need mutual exclusion.  The mutex should be per-channel, but
    here we only use 1 channel. *)
let print_xml =
  let m = Mutex.create () in
  fun oc xml ->
    Mutex.lock m;
    try Xml_printer.print oc xml; Mutex.unlock m
    with e -> let e = Errors.push e in Mutex.unlock m; iraise e


let slave_logger xml_oc level message =
  (* convert the message into XML *)
  let msg = string_of_ppcmds (hov 0 message) in
  let message = {
    Pp.message_level = level;
    Pp.message_content = msg;
  } in
  let () = pr_debug (Printf.sprintf "-> %S" msg) in
  let xml = Pp.of_message message in
  print_xml xml_oc xml

let slave_feeder xml_oc msg =
  let xml = Feedback.of_feedback msg in
  print_xml xml_oc xml

(** The main loop *)

(** Exceptions during eval_call should be converted into [Interface.Fail]
    messages by [handle_exn] above. Otherwise, we die badly, without
    trying to answer malformed requests. *)

let loop () =
  init_signal_handler ();
  catch_break := false;
  let in_ch, out_ch = Spawned.get_channels () in
  let xml_oc = Xml_printer.make (Xml_printer.TChannel out_ch) in
  let in_lb = Lexing.from_function (fun s len ->
    CThread.thread_friendly_read in_ch s ~off:0 ~len) in
  let xml_ic = Xml_parser.make (Xml_parser.SLexbuf in_lb) in
  let () = Xml_parser.check_eof xml_ic false in
  set_logger (slave_logger xml_oc);
  set_feeder (slave_feeder xml_oc);
  (* We'll handle goal fetching and display in our own way *)
  Vernacentries.enable_goal_printing := false;
  Vernacentries.qed_display_script := false;
  while not !quit do
    try
      let xml_query = Xml_parser.parse xml_ic in
(*       pr_with_pid (Xml_printer.to_string_fmt xml_query); *)
      let q = Xmlprotocol.to_call xml_query in
      let () = pr_debug_call q in
      let r = eval_call xml_oc (slave_logger xml_oc Pp.Notice) q in
      let () = pr_debug_answer q r in
(*       pr_with_pid (Xml_printer.to_string_fmt (Xmlprotocol.of_answer q r)); *)
      print_xml xml_oc (Xmlprotocol.of_answer q r);
      flush out_ch
    with
      | Xml_parser.Error (Xml_parser.Empty, _) ->
        pr_debug "End of input, exiting gracefully.";
        exit 0
      | Xml_parser.Error (err, loc) ->
        pr_debug ("Syntax error in query: " ^ Xml_parser.error_msg err);
        exit 1
      | Serialize.Marshal_error ->
        pr_debug "Incorrect query.";
        exit 1
      | any ->
        pr_debug ("Fatal exception in coqtop:\n" ^ Printexc.to_string any);
        exit 1
  done;
  pr_debug "Exiting gracefully.";
  exit 0

let rec parse = function
  | "--help-XML-protocol" :: rest ->
        Xmlprotocol.document Xml_printer.to_string_fmt; exit 0
  | x :: rest -> x :: parse rest
  | [] -> []

let () = Coqtop.toploop_init := (fun args ->
        let args = parse args in
        Flags.make_silent true;
        init_stdout ();
        CoqworkmgrApi.(init Flags.High);
        args)

let () = Coqtop.toploop_run := loop

let () = Usage.add_to_usage "coqidetop" "  --help-XML-protocol    print the documentation of the XML protocol used by CoqIDE\n"
