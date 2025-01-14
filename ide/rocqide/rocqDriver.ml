(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ideutils
open Preferences

let ideslave_rocqtop_flags = ref None

(** * Version *)

let get_version () =
  try
    (* the following makes sense only when running with local layout *)
    let rocqroot = Filename.concat
      (Filename.dirname Sys.executable_name)
      Filename.parent_dir_name
    in
    let ch = open_in (Filename.concat rocqroot "revision") in
    let ver = input_line ch in
    let rev = input_line ch in
    close_in ch;
    Printf.sprintf "%s (%s)" ver rev
  with _ -> Coq_config.version

let short_version () =
  Printf.sprintf "The Coq Proof Assistant, version %s\n" (get_version ())

let version () =
    Printf.sprintf
      "The Coq Proof Assistant, version %s\
       \nArchitecture %s running %s operating system\
       \nGtk version is %s\
       \nThis is %s \n"
      (get_version ())
      Coq_config.arch Sys.os_type
      (let x,y,z = GMain.Main.version in Printf.sprintf "%d.%d.%d" x y z)
      (Filename.basename Sys.executable_name)

(** * Initial checks by launching test rocqtop processes *)

let rec read_all_lines in_chan =
  try
    let arg = input_line in_chan in
    let len = String.length arg  in
    let arg =
      if len > 0 && arg.[len - 1] = '\r' then
        String.sub arg 0 (len - 1)
      else arg
    in
    arg::(read_all_lines in_chan)
  with End_of_file -> []

let rocq_error_popup ~code ~msg data =
  let callback _ = exit code in
  let popup = GWindow.dialog () in
  let button = GButton.button ~stock:`OK ~packing:popup#action_area#add () in
  let _ = GMisc.label ~text:msg ~packing:popup#vbox#add () in
  let container = GPack.notebook ~packing:popup#vbox#add () in
  let iter (label, data) =
    let scroll = GBin.scrolled_window ~hpolicy:`NEVER ~vpolicy:`AUTOMATIC ~height:500 () in
    let label = GMisc.label ~text:label () in
    let text = GText.view ~editable:false ~packing:scroll#add_with_viewport () in
    let () = text#buffer#set_text data in
    ignore (container#append_page ~tab_label:label#coerce scroll#coerce)
  in
  let () = List.iter iter data in
  let _ = popup#connect#destroy ~callback in
  let _ = button#connect#clicked ~callback in
  let _ = popup#run () in
  callback ()

let connection_error cmd lines exn =
  rocq_error_popup ~code:1 ~msg:"Connection with coqtop failed!"
    [
      "Command", cmd;
      "Answer", (String.concat "\n" lines);
      "Exception", Printexc.to_string exn
    ]

let display_rocqtop_answer cmd lines =
  rocq_error_popup ~code:0 ~msg:"The coqtop process has exited."
    [
      "Command", cmd;
      "Answer", String.concat "\n" lines;
    ]

let rec filter_rocq_opts args =
  let argstr = String.concat " " (List.map Filename.quote args) in
  let cmd = Filename.quote (rocqtop_path ()) ^" -q -nois -batch " ^ argstr in
  let cmd = requote cmd in
  let filtered_args = ref [] in
  let errlines = ref [] in
  try
    let oc,ic,ec = Unix.open_process_full cmd (Unix.environment ()) in
    filtered_args := read_all_lines oc;
    errlines := read_all_lines ec;
    match Unix.close_process_full (oc,ic,ec) with
      | Unix.WEXITED 0 -> !filtered_args
      | Unix.WEXITED 127 -> asks_for_rocqtop args
      | _ -> display_rocqtop_answer cmd (!filtered_args @ !errlines)
  with Sys_error _ -> asks_for_rocqtop args
    | e -> connection_error cmd (!filtered_args @ !errlines) e

and asks_for_rocqtop args =
  let pb_mes = GWindow.message_dialog
    ~message:"Failed to load coqidetop. Reset the preference to default?"
    ~message_type:`QUESTION ~buttons:GWindow.Buttons.yes_no () in
  match pb_mes#run () with
    | `YES ->
      let () = cmd_rocqtop#set None in
      let () = custom_rocqtop := None in
      let () = pb_mes#destroy () in
      filter_rocq_opts args
    | `DELETE_EVENT | `NO ->
      let file = select_file_for_open
        ~title:"coqidetop to execute (edit your preference then)"
        ~filter:false
        ~filename:(rocqtop_path ()) () in
      match file with
      | [file] ->
          let () = custom_rocqtop := Some file in
          filter_rocq_opts args
      | _ -> exit 0

exception WrongExitStatus of string

let print_status = function
  | Unix.WEXITED n -> "WEXITED "^string_of_int n
  | Unix.WSIGNALED n -> "WSIGNALED "^string_of_int n
  | Unix.WSTOPPED n -> "WSTOPPED "^string_of_int n

let check_connection args =
  let lines = ref [] in
  let argstr = String.concat " " (List.map Filename.quote args) in
  let cmd = Filename.quote (rocqtop_path ()) ^ " -batch " ^ argstr in
  let cmd = requote cmd in
  try
    let oc,ic,ec = Unix.open_process_full cmd (Unix.environment ()) in
    lines := read_all_lines oc @ read_all_lines ec;
    match Unix.close_process_full (oc,ic,ec) with
    | Unix.WEXITED 0 -> () (* rocqtop seems ok *)
    | st -> raise (WrongExitStatus (print_status st))
  with e -> connection_error cmd !lines e

(** Useful stuff *)

let ignore_error f arg =
  try ignore (f arg) with _ -> ()

(** An abstract copy of unit.
    This will help ensuring that we do not forget to finally call
    continuations when building tasks in other modules. *)

type void = Void

(** ccb : existential type for a (call + callback) type.

    Reference: http://alan.petitepomme.net/cwn/2004.01.13.html
    To rewrite someday with GADT. *)

type 'a poly_ccb = 'a Xmlprotocol.call * ('a Interface.value -> void)
type 't scoped_ccb = { bind_ccb : 'a. 'a poly_ccb -> 't }
type ccb = { open_ccb : 't. 't scoped_ccb -> 't }

let mk_ccb poly = { open_ccb = fun scope -> scope.bind_ccb poly }
let with_ccb ccb e = ccb.open_ccb e

(* overridden on Windows; see file rocqide_WIN32.c.in *)
let interrupter = ref (fun pid -> Unix.kill pid Sys.sigint)

(* todo: does not work on windows (sigusr1 not supported) *)
let breaker = ref (fun pid -> Unix.kill pid Sys.sigusr1)

(** * The structure describing a rocqtop sub-process *)

module GlibMainLoop = struct
  type async_chan = Glib.Io.channel
  type watch_id = Glib.Io.id
  type condition = Glib.Io.condition
  let add_watch ~callback chan =
    Glib.Io.add_watch ~cond:[`ERR; `HUP; `IN; `NVAL; `PRI] ~callback chan
  let remove_watch x = try Glib.Io.remove x with Glib.GError _ -> ()
  let read_all = Ideutils.io_read_all
  let async_chan_of_file_or_socket fd = Glib.Io.channel_of_descr fd
end

module RocqTop = Spawn.Async(GlibMainLoop)

type handle = {
  proc : RocqTop.process;
  xml_oc : Xml_printer.t;
  mutable alive : bool;
  mutable waiting_for : ccb option; (* last non-debug call + callback *)
  mutable db_waiting_for : ccb option; (* last debug call + callback *)
}

type status = New | Ready | Busy | Closed

type 'a task = handle -> ('a -> void) -> void

type reset_kind = Planned | Unexpected

type rocqtop = {
  (* non quoted command-line arguments of rocqtop *)
  mutable sup_args : string list;
  (* called whenever rocqtop dies *)
  mutable reset_handler : unit task;
  (* called whenever rocqtop sends a feedback message *)
  mutable feedback_handler : Feedback.feedback -> unit;
  (* called when the Ltac debugger sends an input prompt message *)
  mutable debug_prompt_handler : tag:string -> Pp.t -> unit;
  (* actual rocqtop process and its status *)
  mutable handle : handle;
  mutable status : status;
  mutable stopped_in_debugger : bool;
  (* i.e., RocqIDE has received a prompt message *)
  mutable do_when_ready : (unit -> unit) Queue.t;
  (* for debug msgs only; functions are called when rocqtop is Ready *)
  mutable basename : string;
  mutable set_script_editable : bool -> unit;
  mutable restore_bpts : unit -> unit
}

let return (x : 'a) : 'a task =
  (); fun _ k -> k x

let bind (m : 'a task) (f : 'a -> 'b task) : 'b task =
  (); fun h k -> m h (fun x -> f x h k)

let seq (m : unit task) (n : 'a task) : 'a task =
  (); fun h k -> m h (fun () -> n h k)

let lift (f : unit -> 'a) : 'a task =
  (); fun _ k -> k (f ())

(** * Starting / signaling / ending a real rocqtop sub-process *)

(** We simulate a Unix.open_process that also returns the pid of
    the created process. Note: this uses Unix.create_process, which
    doesn't call bin/sh, so args shouldn't be quoted. The process
    cannot be terminated by a Unix.close_process, but rather by a
    kill of the pid.

           >--ide2top_w--[pipe]--ide2top_r-->
    rocqide                                   rocqtop
           <--top2ide_r--[pipe]--top2ide_w--<

    Note: we use Unix.stderr in Unix.create_process to get debug
    messages from the rocqtop's Ide_slave loop.

    NB: it's important to close rocqide's descriptors (ide2top_w and top2ide_r)
    in rocqtop. We do this indirectly via [Unix.set_close_on_exec].
    This way, rocqide has the only remaining copies of these descriptors,
    and closing them later will have visible effects in rocqtop. Cf man 7 pipe :

    - If  all file descriptors referring to the write end of a pipe have been
      closed, then an attempt to read(2) from the pipe will see end-of-file
      (read(2) will return 0).
    - If all file descriptors referring to the read end of a pipe have been
      closed, then a write(2) will cause a SIGPIPE signal to be generated for
      the calling process. If the calling process is ignoring this signal,
      then write(2) fails with the error EPIPE.

    Symmetrically, rocqtop's descriptors (ide2top_r and top2ide_w) should be
    closed in rocqide.
*)

exception TubeError of string
exception AnswerWithoutRequest of string

let rec check_errors = function
| [] -> ()
| (`IN | `PRI) :: conds -> check_errors conds
| `ERR :: _ -> raise (TubeError "ERR")
| `HUP :: _ -> raise (TubeError "HUP")
| `NVAL :: _ -> raise (TubeError "NVAL")
| `OUT :: _ -> raise (TubeError "OUT")

let handle_feedback feedback_processor xml =
  let feedback = Xmlprotocol.to_feedback xml in
  feedback_processor feedback

let handle_ltac_debug ltac_debug_processor xml =
  let tag, msg = Xmlprotocol.to_ltac_debug_answer xml in
  ltac_debug_processor ~tag msg

let handle_final_answer handle xml =
  let () = Minilib.log "Handling rocqtop answer" in
  let ccb = match handle.db_waiting_for, handle.waiting_for with
  | None, None -> raise (AnswerWithoutRequest (Xml_printer.to_string_fmt xml))
  | Some c, _ -> handle.db_waiting_for <- None; c
  | None, Some c -> handle.waiting_for <- None; c in
  with_ccb ccb { bind_ccb = fun (c, f) -> f (Xmlprotocol.to_answer c xml) }

type input_state = {
  mutable fragment : string;
  mutable lexerror : int option;
}

let unsafe_handle_input handle (feedback_processor, ltac_debug_processor) state conds ~read_all =
  check_errors conds;
  let s = read_all () in
  if String.length s = 0 then raise (TubeError "EMPTY");
  let s = state.fragment ^ s in
  state.fragment <- s;
  let lex = Lexing.from_string s in
  let p = Xml_parser.make (Xml_parser.SLexbuf lex) in
  let rec loop () =
    let xml = Xml_parser.parse ~canonicalize:false p in
    let l_end = Lexing.lexeme_end lex in
    state.fragment <- String.sub s l_end (String.length s - l_end);
    state.lexerror <- None;
    match Xmlprotocol.msg_kind xml with
    | Xmlprotocol.Feedback ->
      handle_feedback feedback_processor xml;
      loop ()
    | Xmlprotocol.LtacDebugInfo ->
      handle_ltac_debug ltac_debug_processor xml;
      loop ()
    | Xmlprotocol.Other ->
      ignore (handle_final_answer handle xml);  (* request completed *)
      if handle.waiting_for <> None then (* i.e., just finished a db request *)
        loop ()
  in
  try loop ()
  with Xml_parser.Error _ as e ->
    (* Parsing error at the end of s : we have only received a part of
        an xml answer. We store the current fragment for later *)
    let l_end = Lexing.lexeme_end lex in
    (* Heuristic hack not to reimplement the lexer:  if ever the lexer dies
       twice at the same place, then this is a non-recoverable error *)
    if state.lexerror = Some l_end then raise e;
    state.lexerror <- Some l_end

let print_exception = function
  | Xml_parser.Error e -> Xml_parser.error e
  | Serialize.Marshal_error(expected,actual) ->
      "Protocol violation. Expected: " ^ expected ^ " Actual: "
        ^ Xml_printer.to_string actual
  | e -> Printexc.to_string e

let input_watch handle respawner processors =
  let state = { fragment = ""; lexerror = None; } in
  (fun conds ~read_all ->
    let h = handle () in
    if not h.alive then false
    else
      try unsafe_handle_input h processors state conds ~read_all; true
      with e ->
        Minilib.log ("Rocqtop reader failed, resetting: "^print_exception e);
        respawner ();
        false)

let bind_self_as f =
  let me = ref None in
  let get_me () = Option.get !me in
  me := Some(f get_me);
  Option.get !me

(** This launches a fresh handle from its command line arguments. *)
let spawn_handle args respawner processors =
  let prog = rocqtop_path () in
  let async_default =
    (* disable async processing by default in Windows *)
    if List.mem Sys.os_type ["Win32"; "Cygwin"] then
      "off"
    else
      "on"
  in
  let args = Array.of_list ("--xml_format=Ppcmds" :: "-async-proofs" :: async_default :: args) in
  let env =
    match !ideslave_rocqtop_flags with
    | None -> None
    | Some s ->
      let open Str in
      let open Array in
      let opts = split_delim (regexp ",") s in
      begin try
        let erex = regexp "^extra-env=" in
        let echunk = List.find (fun s -> string_match erex s 0) opts in
        Some (append
          (of_list (split_delim (regexp ";") (replace_first erex "" echunk)))
          (Unix.environment ()))
      with Not_found -> None end in
  bind_self_as (fun handle ->
  let proc, oc =
    RocqTop.spawn ?env prog args (input_watch handle respawner processors) in
  {
    proc;
    xml_oc = Xml_printer.make (Xml_printer.TChannel oc);
    alive = true;
    waiting_for = None;
    db_waiting_for = None;
  })

(** This clears any potentially remaining open garbage. *)
let clear_handle h =
  if h.alive then begin
    (* invalidate the old handle *)
    RocqTop.kill h.proc;
    ignore(RocqTop.wait h.proc);
    h.alive <- false;
    h.db_waiting_for <- None;
  end

let pstatus = function
    | Closed -> "Closed"
    | Busy -> "Busy"
    | Ready -> "Ready"
    | New -> "New"

let can_send_db_msg rocqtop =
  rocqtop.handle.db_waiting_for = None &&
  match rocqtop.status with
  | Busy -> rocqtop.stopped_in_debugger
  | Ready -> true
  | _ -> false

let add_do_when_ready rocqtop hook =
  let q = rocqtop.do_when_ready in
  Queue.add hook q;
  if not (Queue.is_empty q) && can_send_db_msg rocqtop then
    let f = Queue.pop q in f ()

let mkready rocqtop db =
  fun () ->
    if not db then begin
      rocqtop.status <- Ready;
      rocqtop.set_script_editable true
    end;
    if rocqtop.status = Ready || (db && can_send_db_msg rocqtop) then begin
      let q = rocqtop.do_when_ready in
      if not (Queue.is_empty q) then
        let f = Queue.pop q in f ()
    end;
    Void

let save_all = ref (fun () -> assert false)

let rec respawn_rocqtop ?(why=Unexpected) rocqtop =
  let () = match why with
  | Unexpected ->
    let title = "Warning" in
    let icon = (warn_image ())#coerce in
    let buttons = ["Reset"; "Save all and quit"; "Quit without saving"] in
    let ans = GToolbox.question_box ~title ~buttons ~icon (rocqtop.basename ^ ": coqidetop died.") in
    if ans = 2 then (!save_all (); GtkMain.Main.quit ())
    else if ans = 3 then GtkMain.Main.quit ()
  | Planned -> ()
  in
  clear_handle rocqtop.handle;
  Queue.clear rocqtop.do_when_ready;
  ignore_error (fun () ->
     let processors = (rocqtop.feedback_handler, rocqtop.debug_prompt_handler) in
     rocqtop.handle <-
       spawn_handle
         rocqtop.sup_args
         (fun () -> respawn_rocqtop rocqtop)
         processors) ();
  (* Normally, the handle is now a fresh one.
     If not, there isn't much we can do ... *)
  assert (rocqtop.handle.alive = true);
  rocqtop.status <- New;
  rocqtop.set_script_editable true;
  ignore (rocqtop.reset_handler rocqtop.handle (mkready rocqtop false));
  rocqtop.restore_bpts ()  (* queue call to restore previous breakpoints *)

let spawn_rocqtop basename sup_args =
  bind_self_as (fun this ->
      let processors =
        (fun msg -> (this ()).feedback_handler msg)
      , (fun ~tag msg -> (this ()).debug_prompt_handler ~tag msg)
      in
  {
    handle = spawn_handle sup_args
               (fun () -> respawn_rocqtop (this ()))
               processors;
    sup_args;
    reset_handler = (fun _ k -> k ());
    feedback_handler = (fun _ -> ());
    debug_prompt_handler = (fun ~tag:_ _ -> ());
    status = New;
    stopped_in_debugger = false;
    do_when_ready = Queue.create ();
    basename;
    set_script_editable = (fun v -> failwith "set_script_editable");
    restore_bpts = (fun _ -> failwith "restore_bpts")
  })

let set_restore_bpts rocqtop f = rocqtop.restore_bpts <- f

let set_reset_handler rocqtop hook = rocqtop.reset_handler <- hook

let set_feedback_handler rocqtop hook = rocqtop.feedback_handler <- hook
let set_debug_prompt_handler rocqtop hook = rocqtop.debug_prompt_handler <- hook

let setup_script_editable rocqtop f = rocqtop.set_script_editable <- f

let is_computing rocqtop = (rocqtop.status = Busy)

let is_stopped_in_debugger rocqtop = rocqtop.stopped_in_debugger

let is_ready_or_stopped_in_debugger rocqtop =
  rocqtop.status = Ready || (is_stopped_in_debugger rocqtop)

let set_stopped_in_debugger rocqtop v =
  rocqtop.stopped_in_debugger <- v

(* For closing a rocqtop, we don't try to send it a Quit call anymore,
   but rather close its channels:
    - a listening rocqtop will handle this just as a Quit call
    - a busy rocqtop will anyway have to be killed *)

let close_rocqtop rocqtop =
  rocqtop.status <- Closed;
  clear_handle rocqtop.handle

let reset_rocqtop rocqtop = respawn_rocqtop ~why:Planned rocqtop

let get_arguments rocqtop = rocqtop.sup_args

let set_arguments rocqtop args =
  rocqtop.sup_args <- args;
  reset_rocqtop rocqtop

let process_task ?(db=false) rocqtop task =
  (* todo: queuing is probably better than assert. *)
  if not (rocqtop.status = Ready || rocqtop.status = New || (db && rocqtop.status = Busy)) then
    Printf.printf "Assert failure in process_task rocqtop.status = %s db = %b\n" (pstatus rocqtop.status) db;
  assert (rocqtop.status = Ready || rocqtop.status = New || (db && rocqtop.status = Busy));
  if not db then begin
    rocqtop.status <- Busy;
    rocqtop.set_script_editable false
  end;
  try ignore (task rocqtop.handle (mkready rocqtop db))
  with e ->
    Minilib.log ("Rocqtop writer failed, resetting: " ^ Printexc.to_string e);
    if rocqtop.status <> Closed then respawn_rocqtop rocqtop

(* todo: logic for functions such as "forward one" should not rely on try_grab
   to discard the request; a small amount of queuing would make this a trivial
   routine, perhaps not even needed.  The "abort" should go away. *)
let try_grab ?(db=false) rocqtop task abort =
  match rocqtop.status with
    | _ when db && rocqtop.handle.db_waiting_for <> None -> (abort (); false)
    | Closed -> abort (); false
    | Busy when db ->
      if (*rocqtop.stopped_in_debugger &&*) rocqtop.handle.db_waiting_for = None then
        (process_task ~db rocqtop task; true)
      else
        (abort (); false)
    | Busy | New -> abort (); false
    | Ready -> process_task ~db rocqtop task; true

let init_rocqtop rocqtop task =
  assert (rocqtop.status = New);
  process_task rocqtop task

(** * Calls to rocqtop *)

(** Cf [Ide_intf] for more details *)

type 'a query = 'a Interface.value task

(* todo: it's too easy to fail the asserts here when changing the code.
   We should look at making handle.waiting_for and handle.db_waiting_for into
   queues, perhaps have a queue for the call to Xml_printer.print with flow
   control.  Then rocqtop.do_when_ready would not be needed and other
   logic such as mkready and rocqtop initialization might be simplified. *)

let eval_call ?(db=false) call handle k =
  (* Send messages to rocqtop and prepare the decoding of the answer *)
  let in_db = if db then "db " else "" in
  Minilib.log ("Start " ^ in_db ^ "eval_call " ^ Xmlprotocol.pr_call call);
  if db then begin
    assert (handle.alive && handle.db_waiting_for = None);
    handle.db_waiting_for <- Some (mk_ccb (call,k))
  end else begin
    assert (handle.alive && handle.waiting_for = None);
    handle.waiting_for <- Some (mk_ccb (call,k))
  end;
  Xml_printer.print handle.xml_oc (Xmlprotocol.of_call call);
  Minilib.log ("End " ^ in_db ^ "eval_call");
  Void

let add x = eval_call (Xmlprotocol.add x)
let edit_at i = eval_call (Xmlprotocol.edit_at i)
let query x = eval_call (Xmlprotocol.query x)
let mkcases s = eval_call (Xmlprotocol.mkcases s)
let status force = eval_call (Xmlprotocol.status force)
let hints x = eval_call (Xmlprotocol.hints x)
let search flags = eval_call (Xmlprotocol.search flags)
let init x = eval_call (Xmlprotocol.init x)
let stop_worker x = eval_call (Xmlprotocol.stop_worker x)
let proof_diff x = eval_call (Xmlprotocol.proof_diff x)
let db_cmd x = eval_call ~db:true (Xmlprotocol.db_cmd x)
let db_upd_bpts x = eval_call ~db:true (Xmlprotocol.db_upd_bpts x)
let db_continue x = eval_call ~db:true (Xmlprotocol.db_continue x)
let db_stack x = eval_call ~db:true (Xmlprotocol.db_stack x)
let db_vars x = eval_call ~db:true (Xmlprotocol.db_vars x)
let db_configd x = eval_call ~db:true (Xmlprotocol.db_configd x)

let interrupt_rocqtop rocqtop workers =
  if rocqtop.status = Busy then
    try !interrupter (RocqTop.unixpid rocqtop.handle.proc)
    with _ -> Minilib.log "Error while sending Ctrl-C"
  else
    let rec aux = function
    | [] -> Void
    | w :: ws -> stop_worker w rocqtop.handle (fun _ -> aux ws)
    in
      let Void = aux workers in ()

let send_break rocqtop =
  try
    !breaker (RocqTop.unixpid rocqtop.handle.proc)
  with _ -> Minilib.log "Error while sending Break"

module PrintOpt =
struct
  type _ t =
  | BoolOpt : string list -> bool t
  | StringOpt : string list -> string t

  let opt_name (type a) : a t -> string list = function
  | BoolOpt l -> l
  | StringOpt l -> l

  let opt_data (type a) (key : a t) (v : a) = match key with
  | BoolOpt l -> Interface.BoolValue v
  | StringOpt l -> Interface.StringValue v

  (* Boolean options *)

  let implicit = BoolOpt ["Printing"; "Implicit"]
  let coercions = BoolOpt ["Printing"; "Coercions"]
  let nested_matching = BoolOpt ["Printing"; "Matching"]
  let notations = BoolOpt ["Printing"; "Notations"]
  let parentheses = BoolOpt ["Printing"; "Parentheses"]
  let all_basic = BoolOpt ["Printing"; "All"]
  let existential = BoolOpt ["Printing"; "Existential"; "Instances"]
  let universes = BoolOpt ["Printing"; "Universes"]
  let unfocused = BoolOpt ["Printing"; "Unfocused"]
  let goal_names = BoolOpt ["Printing"; "Goal"; "Names"]
  let record = BoolOpt ["Printing"; "Records"]
  let synth = BoolOpt ["Printing"; "Synth"]
  let diff = StringOpt ["Diffs"]

  type 'a descr = { opts : 'a t list; init : 'a; label : string }

  let bool_items = [
    { opts = [implicit]; init = false; label = "Display _implicit arguments" };
    { opts = [coercions]; init = false; label = "Display _coercions" };
    { opts = [nested_matching]; init = true;
      label = "Display nested _matching expressions" };
    { opts = [notations]; init = true; label = "Display _notations" };
    { opts = [parentheses]; init = false; label = "Display _parentheses" };
    { opts = [all_basic]; init = false;
      label = "Display _all basic low-level contents" };
    { opts = [existential]; init = false;
      label = "Display _existential variable instances" };
    { opts = [universes]; init = false; label = "Display _universe levels" };
    { opts = [all_basic;existential;universes]; init = false;
      label = "Display all _low-level contents" };
    { opts = [unfocused]; init = false; label = "Display un_focused goals" };
    { opts = [goal_names]; init = false; label = "Display _goal names" };
    { opts = [record]; init = true; label = "Use _record syntax" };
    { opts = [synth]; init = true; label = "Hide _synthesizable types" }
  ]

  let diff_item = { opts = [diff]; init = "off"; label = "Display _proof diffs" }

  (** The current status of the boolean options *)

  let current_state = Hashtbl.create 11

  let set (type a) (opt : a t) (v : a) =
    Hashtbl.replace current_state (opt_name opt) (opt_data opt v)

  let get (type a) (opt : a t) =
    Hashtbl.find current_state (opt_name opt)

  let reset () =
    let init_descr d = List.iter (fun o -> set o d.init) d.opts in
    List.iter init_descr bool_items;
    List.iter (fun o -> set o diff_item.init) diff_item.opts

  let _ = reset ()

  let printing_unfocused () =
  let BoolOpt unfocused = unfocused in
  match Hashtbl.find current_state unfocused with
  | Interface.BoolValue b -> b
  | _ -> assert false

  (** Transmitting options to rocqtop *)

  (* todo: if Rocq hasn't processed any statements since the last enforce,
     it's unnecessary to send another.  In particular, "goals" and "evars"
     below are generally called one after the other. *)
  let enforce h k =
    let mkopt o v acc = (o, v) :: acc in
    let opts = List.sort (fun a b ->
          String.compare (String.concat " " (fst a)) (String.concat " " (fst b)))
        (Hashtbl.fold mkopt current_state []) in
    eval_call (Xmlprotocol.set_options opts) h
      (function
        | Interface.Good () -> k ()
        | _ -> failwith "Cannot set options. Resetting rocqtop")

end

let goals x h k =
  PrintOpt.enforce h (fun () -> eval_call (Xmlprotocol.goals x) h k)

let subgoals x h k =
  PrintOpt.enforce h (fun () -> eval_call (Xmlprotocol.subgoals x) h k)

let evars x h k =
  PrintOpt.enforce h (fun () -> eval_call (Xmlprotocol.evars x) h k)
