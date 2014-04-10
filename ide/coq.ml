(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Ideutils
open Preferences

(** * Version and date *)

let get_version_date () =
  let date =
    if Glib.Utf8.validate Coq_config.date
    then Coq_config.date
    else "<date not printable>" in
  try
    (* the following makes sense only when running with local layout *)
    let coqroot = Filename.concat
      (Filename.dirname Sys.executable_name)
      Filename.parent_dir_name
    in
    let ch = open_in (Filename.concat coqroot "revision") in
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
       \nThis is %s (%s is the best one for this architecture and OS)\
       \n"
      ver date
      Coq_config.arch Sys.os_type
      (let x,y,z = GMain.Main.version in Printf.sprintf "%d.%d.%d" x y z)
      (Filename.basename Sys.executable_name)
      Coq_config.best


(** * Initial checks by launching test coqtop processes *)

let rec read_all_lines in_chan =
  try
    let arg = input_line in_chan in
    let len = String.length arg  in
    let arg =
      if arg.[len - 1] = '\r' then
	String.sub arg 0 (len - 1)
      else arg
    in
    arg::(read_all_lines in_chan)
  with End_of_file -> []

let fatal_error_popup msg =
  let popup = GWindow.message_dialog ~buttons:GWindow.Buttons.ok
    ~message_type:`ERROR ~message:msg ()
  in ignore (popup#run ()); exit 1

let final_info_popup small msg =
  if small then
    let popup = GWindow.message_dialog ~buttons:GWindow.Buttons.ok
      ~message_type:`INFO ~message:msg ()
    in
    let _ = popup#run () in
    exit 0
  else
    let popup = GWindow.dialog () in
    let button = GButton.button ~label:"ok" ~packing:popup#action_area#add ()
    in
    let scroll = GBin.scrolled_window ~hpolicy:`NEVER ~vpolicy:`AUTOMATIC
      ~packing:popup#vbox#add ~height:500 ()
    in
    let _ = GMisc.label ~text:msg ~packing:scroll#add_with_viewport () in
    let _ = popup#connect#destroy ~callback:(fun _ -> exit 0) in
    let _ = button#connect#clicked ~callback:(fun _ -> exit 0) in
    let _ = popup#run () in
    exit 0

let connection_error cmd lines exn =
  fatal_error_popup
    ("Connection with coqtop failed!\n"^
     "Command was: "^cmd^"\n"^
     "Answer was: "^(String.concat "\n  " lines)^"\n"^
     "Exception was: "^Printexc.to_string exn)

let display_coqtop_answer cmd lines =
  final_info_popup (List.length lines < 30)
    ("Coqtop exited\n"^
     "Command was: "^cmd^"\n"^
     "Answer was: "^(String.concat "\n  " lines))

let check_remaining_opt arg =
  if arg <> "" && arg.[0] = '-' then fatal_error_popup ("Illegal option: "^arg)

let rec filter_coq_opts args =
  let argstr = String.concat " " (List.map Filename.quote args) in
  let cmd = Filename.quote (coqtop_path ()) ^" -nois -filteropts " ^ argstr in
  let cmd = requote cmd in
  let filtered_args = ref [] in
  let errlines = ref [] in
  try
    let oc,ic,ec = Unix.open_process_full cmd (Unix.environment ()) in
    filtered_args := read_all_lines oc;
    errlines := read_all_lines ec;
    match Unix.close_process_full (oc,ic,ec) with
      | Unix.WEXITED 0 -> !filtered_args
      | Unix.WEXITED 127 -> asks_for_coqtop args
      | _ -> display_coqtop_answer cmd (!filtered_args @ !errlines)
  with Sys_error _ -> asks_for_coqtop args
    | e -> connection_error cmd (!filtered_args @ !errlines) e

and asks_for_coqtop args =
  let pb_mes = GWindow.message_dialog
    ~message:"Failed to load coqtop. Reset the preference to default ?"
    ~message_type:`QUESTION ~buttons:GWindow.Buttons.yes_no () in
  match pb_mes#run () with
    | `YES ->
      let () = current.cmd_coqtop  <- None in
      let () = custom_coqtop := None in
      let () = pb_mes#destroy () in
      filter_coq_opts args
    | `DELETE_EVENT | `NO ->
      let () = pb_mes#destroy () in
      let cmd_sel = GWindow.file_selection
	~title:"Coqtop to execute (edit your preference then)"
	~filename:(coqtop_path ()) ~urgency_hint:true () in
      match cmd_sel#run () with
	| `OK ->
	  let () = custom_coqtop := (Some cmd_sel#filename) in
	  let () = cmd_sel#destroy () in
	  filter_coq_opts args
	| `CANCEL | `DELETE_EVENT | `HELP -> exit 0

exception WrongExitStatus of string

let print_status = function
  | Unix.WEXITED n -> "WEXITED "^string_of_int n
  | Unix.WSIGNALED n -> "WSIGNALED "^string_of_int n
  | Unix.WSTOPPED n -> "WSTOPPED "^string_of_int n

let check_connection args =
  let lines = ref [] in
  let argstr = String.concat " " (List.map Filename.quote args) in
  let cmd = Filename.quote (coqtop_path ()) ^ " -batch " ^ argstr in
  let cmd = requote cmd in
  try
    let ic = Unix.open_process_in cmd in
    lines := read_all_lines ic;
    match Unix.close_process_in ic with
    | Unix.WEXITED 0 -> () (* coqtop seems ok *)
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

type 'a poly_ccb = 'a Serialize.call * ('a Interface.value -> void)
type 't scoped_ccb = { bind_ccb : 'a. 'a poly_ccb -> 't }
type ccb = { open_ccb : 't. 't scoped_ccb -> 't }

let mk_ccb poly = { open_ccb = fun scope -> scope.bind_ccb poly }
let with_ccb ccb e = ccb.open_ccb e

let interrupter = ref (fun pid -> Unix.kill pid Sys.sigint)

(** * The structure describing a coqtop sub-process *)

let gio_channel_of_descr_socket = ref Glib.Io.channel_of_descr

module GlibMainLoop = struct
  type async_chan = Glib.Io.channel
  type watch_id = Glib.Io.id
  type condition = Glib.Io.condition
  let add_watch ~callback chan =
    Glib.Io.add_watch ~cond:[`ERR; `HUP; `IN; `NVAL; `PRI] ~callback chan
  let remove_watch x = try Glib.Io.remove x with Glib.GError _ -> ()
  let read_all = Ideutils.io_read_all
  let async_chan_of_file fd = Glib.Io.channel_of_descr fd
  let async_chan_of_socket s = !gio_channel_of_descr_socket s
  let add_timeout ~sec callback =
    ignore(Glib.Timeout.add ~ms:(sec * 1000) ~callback)
end

module CoqTop = Spawn.Async(GlibMainLoop)

type handle = {
  proc : CoqTop.process;
  xml_oc : Xml_printer.t;
  mutable alive : bool;
  mutable waiting_for : (ccb * logger) option; (* last call + callback + log *)
}

(** Coqtop process status :
  - New    : a process has been spawned, but not initialized via [init_coqtop].
             It will reject tasks given via [try_grab].
  - Ready  : no current task, accepts new tasks via [try_grab].
  - Busy   : has accepted a task via [init_coqtop] or [try_grab],
             It will reject other tasks for the moment
  - Closed : the coqide buffer has been closed, we discard any further task.
*)

type status = New | Ready | Busy | Closed

type 'a task = handle -> ('a -> void) -> void

type reset_kind = Planned | Unexpected

type coqtop = {
  (* non quoted command-line arguments of coqtop *)
  mutable sup_args : string list;
  (* called whenever coqtop dies *)
  mutable reset_handler : reset_kind -> unit task;
  (* called whenever coqtop sends a feedback message *)
  mutable feedback_handler : Interface.feedback -> unit;
  (* actual coqtop process and its status *)
  mutable handle : handle;
  mutable status : status;
}

let return (x : 'a) : 'a task =
  (); fun _ k -> k x

let bind (m : 'a task) (f : 'a -> 'b task) : 'b task =
  (); fun h k -> m h (fun x -> f x h k)

let seq (m : unit task) (n : 'a task) : 'a task =
  (); fun h k -> m h (fun () -> n h k)

let lift (f : unit -> 'a) : 'a task =
  (); fun _ k -> k (f ())

(** * Starting / signaling / ending a real coqtop sub-process *)

(** We simulate a Unix.open_process that also returns the pid of
    the created process. Note: this uses Unix.create_process, which
    doesn't call bin/sh, so args shouldn't be quoted. The process
    cannot be terminated by a Unix.close_process, but rather by a
    kill of the pid.

           >--ide2top_w--[pipe]--ide2top_r-->
    coqide                                   coqtop
           <--top2ide_r--[pipe]--top2ide_w--<

    Note: we use Unix.stderr in Unix.create_process to get debug
    messages from the coqtop's Ide_slave loop.

    NB: it's important to close coqide's descriptors (ide2top_w and top2ide_r)
    in coqtop. We do this indirectly via [Unix.set_close_on_exec].
    This way, coqide has the only remaining copies of these descriptors,
    and closing them later will have visible effects in coqtop. Cf man 7 pipe :

    - If  all file descriptors referring to the write end of a pipe have been
      closed, then an attempt to read(2) from the pipe will see end-of-file
      (read(2) will return 0).
    - If all file descriptors referring to the read end of a pipe have been
      closed, then a write(2) will cause a SIGPIPE signal to be generated for
      the calling process. If the calling process is ignoring this signal,
      then write(2) fails with the error EPIPE.

    Symmetrically, coqtop's descriptors (ide2top_r and top2ide_w) should be
    closed in coqide.
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

let handle_intermediate_message handle xml =
  let message = Serialize.to_message xml in
  let level = message.Interface.message_level in
  let content = message.Interface.message_content in
  let logger = match handle.waiting_for with
    | Some (_, l) -> l 
    | None -> function
        | Interface.Error -> Minilib.log ~level:`ERROR
        | Interface.Info -> Minilib.log ~level:`INFO
        | Interface.Notice -> Minilib.log ~level:`NOTICE
        | Interface.Warning -> Minilib.log ~level:`WARNING
        | Interface.Debug _ -> Minilib.log ~level:`DEBUG
  in
  logger level content

let handle_feedback feedback_processor xml =
  let feedback = Serialize.to_feedback xml in
  feedback_processor feedback

let handle_final_answer handle xml =
  let () = Minilib.log "Handling coqtop answer" in
  let ccb = match handle.waiting_for with
    | None -> raise (AnswerWithoutRequest (Xml_printer.to_string_fmt xml))
    | Some (c, _) -> c in
  let () = handle.waiting_for <- None in
  with_ccb ccb { bind_ccb = fun (c, f) -> f (Serialize.to_answer c xml) }

type input_state = {
  mutable fragment : string;
  mutable lexerror : int option;
}

let unsafe_handle_input handle feedback_processor state conds ~read_all =
  check_errors conds;
  let s = read_all () in
  if String.length s = 0 then raise (TubeError "EMPTY");
  let s = state.fragment ^ s in
  state.fragment <- s;
  let lex = Lexing.from_string s in
  let p = Xml_parser.make (Xml_parser.SLexbuf lex) in
  let rec loop () =
    let xml = Xml_parser.parse p in
    let l_end = Lexing.lexeme_end lex in
    state.fragment <- String.sub s l_end (String.length s - l_end);
    state.lexerror <- None;
    if Serialize.is_message xml then begin
      handle_intermediate_message handle xml;
      loop ()
    end else if Serialize.is_feedback xml then begin
      handle_feedback feedback_processor xml;
      loop ()
    end else begin
      ignore (handle_final_answer handle xml)
    end
  in
  try loop ()
  with Xml_parser.Error _ as e ->
    (* Parsing error at the end of s : we have only received a part of
        an xml answer. We store the current fragment for later *)
    let l_end = Lexing.lexeme_end lex in
    (** Heuristic hack not to reimplement the lexer:  if ever the lexer dies
        twice at the same place, then this is a non-recoverable error *)
    if state.lexerror = Some l_end then raise e;
    state.lexerror <- Some l_end

let print_exception = function
  | Xml_parser.Error e -> Xml_parser.error e
  | Serialize.Marshal_error -> "Protocol violation"
  | e -> Printexc.to_string e

let input_watch handle respawner feedback_processor =
  let state = { fragment = ""; lexerror = None; } in
  (fun conds ~read_all ->
    let h = handle () in
    if not h.alive then false
    else
      try unsafe_handle_input h feedback_processor state conds ~read_all; true
      with e ->
        Minilib.log ("Coqtop reader failed, resetting: "^print_exception e);
        respawner ();
        false)

let bind_self_as f =
  let me = ref None in
  let get_me () = Option.get !me in
  me := Some(f get_me);
  Option.get !me

(** This launches a fresh handle from its command line arguments. *)
let spawn_handle args respawner feedback_processor =
  let prog = coqtop_path () in
  let args = Array.of_list ("-async-proofs" :: "on" :: "-ideslave" :: args) in
  let env =
    match !Flags.ideslave_coqtop_flags with
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
    CoqTop.spawn ?env prog args (input_watch handle respawner feedback_processor) in
  {
    proc;
    xml_oc = Xml_printer.make (Xml_printer.TChannel oc);
    alive = true;
    waiting_for = None;
  })

(** This clears any potentially remaining open garbage. *)
let clear_handle h =
  if h.alive then begin
    (* invalidate the old handle *)
    CoqTop.kill h.proc;
    ignore(CoqTop.wait h.proc);
    h.alive <- false;
  end

let mkready coqtop =
  fun () -> coqtop.status <- Ready; Void

let rec respawn_coqtop ?(why=Unexpected) coqtop =
  clear_handle coqtop.handle;
  ignore_error (fun () ->
     coqtop.handle <-
       spawn_handle
         coqtop.sup_args
         (fun () -> respawn_coqtop coqtop)
         coqtop.feedback_handler) ();
  (* Normally, the handle is now a fresh one.
     If not, there isn't much we can do ... *)
  assert (coqtop.handle.alive = true);
  coqtop.status <- New;
  ignore (coqtop.reset_handler why coqtop.handle (mkready coqtop))

let spawn_coqtop sup_args =
  bind_self_as (fun this -> {
    handle = spawn_handle sup_args
               (fun () -> respawn_coqtop (this ()))
               (fun msg -> (this ()).feedback_handler msg);
    sup_args = sup_args;
    reset_handler = (fun _ _ k -> k ());
    feedback_handler = (fun _ -> ());
    status = New;
  })

let set_reset_handler coqtop hook = coqtop.reset_handler <- hook

let set_feedback_handler coqtop hook = coqtop.feedback_handler <- hook

let is_computing coqtop = (coqtop.status = Busy)

(* For closing a coqtop, we don't try to send it a Quit call anymore,
   but rather close its channels:
    - a listening coqtop will handle this just as a Quit call
    - a busy coqtop will anyway have to be killed *)

let close_coqtop coqtop =
  coqtop.status <- Closed;
  clear_handle coqtop.handle

let reset_coqtop coqtop = respawn_coqtop ~why:Planned coqtop

let break_coqtop coqtop =
  try !interrupter (CoqTop.unixpid coqtop.handle.proc)
  with _ -> Minilib.log "Error while sending Ctrl-C"

let get_arguments coqtop = coqtop.sup_args

let set_arguments coqtop args =
  coqtop.sup_args <- args;
  reset_coqtop coqtop

let process_task coqtop task =
  assert (coqtop.status = Ready || coqtop.status = New);
  coqtop.status <- Busy;
  try ignore (task coqtop.handle (mkready coqtop))
  with e ->
    Minilib.log ("Coqtop writer failed, resetting: " ^ Printexc.to_string e);
    if coqtop.status <> Closed then respawn_coqtop coqtop

let try_grab coqtop task abort =
  match coqtop.status with
    |Closed -> ()
    |Busy|New -> abort ()
    |Ready -> process_task coqtop task

let init_coqtop coqtop task =
  assert (coqtop.status = New);
  process_task coqtop task

(** * Calls to coqtop *)

(** Cf [Ide_intf] for more details *)

type 'a query = 'a Interface.value task

let eval_call ?(logger=default_logger) call handle k =
  (** Send messages to coqtop and prepare the decoding of the answer *)
  Minilib.log ("Start eval_call " ^ Serialize.pr_call call);
  assert (handle.alive && handle.waiting_for = None);
  handle.waiting_for <- Some (mk_ccb (call,k), logger);
  Xml_printer.print handle.xml_oc (Serialize.of_call call);
  Minilib.log "End eval_call";
  Void

let add ?(logger=default_logger) x = eval_call ~logger (Serialize.add x)
let edit_at i = eval_call (Serialize.edit_at i)
let query ?(logger=default_logger) x = eval_call ~logger (Serialize.query x)
let mkcases s = eval_call (Serialize.mkcases s)
let status ?logger force = eval_call ?logger (Serialize.status force)
let hints x = eval_call (Serialize.hints x)
let search flags = eval_call (Serialize.search flags)
let init x = eval_call (Serialize.init x)
let stop_worker x = eval_call (Serialize.stop_worker x)

module PrintOpt =
struct
  type t = string list

  (* Boolean options *)

  let implicit = ["Printing"; "Implicit"]
  let coercions = ["Printing"; "Coercions"]
  let raw_matching = ["Printing"; "Matching"]
  let notations = ["Printing"; "Notations"]
  let all_basic = ["Printing"; "All"]
  let existential = ["Printing"; "Existential"; "Instances"]
  let universes = ["Printing"; "Universes"]

  type bool_descr = { opts : t list; init : bool; label : string }

  let bool_items = [
    { opts = [implicit]; init = false; label = "Display _implicit arguments" };
    { opts = [coercions]; init = false; label = "Display _coercions" };
    { opts = [raw_matching]; init = true;
      label = "Display raw _matching expressions" };
    { opts = [notations]; init = true; label = "Display _notations" };
    { opts = [all_basic]; init = false;
      label = "Display _all basic low-level contents" };
    { opts = [existential]; init = false;
      label = "Display _existential variable instances" };
    { opts = [universes]; init = false; label = "Display _universe levels" };
    { opts = [all_basic;existential;universes]; init = false;
      label = "Display all _low-level contents" }
  ]

  (** The current status of the boolean options *)

  let current_state = Hashtbl.create 11

  let set opt v = Hashtbl.replace current_state opt v

  let reset () =
    let init_descr d = List.iter (fun o -> set o d.init) d.opts in
    List.iter init_descr bool_items

  let _ = reset ()

  (** Integer option *)

  let width = ["Printing"; "Width"]
  let width_state = ref None
  let set_printing_width w = width_state := Some w

  (** Transmitting options to coqtop *)

  let enforce h k =
    let mkopt o v acc = (o, Interface.BoolValue v) :: acc in
    let opts = Hashtbl.fold mkopt current_state [] in
    let opts = (width, Interface.IntValue !width_state) :: opts in
    eval_call (Serialize.set_options opts) h
      (function
	| Interface.Good () -> k ()
	| _ -> failwith "Cannot set options. Resetting coqtop")

end

let goals ?logger x h k =
  PrintOpt.enforce h (fun () -> eval_call ?logger (Serialize.goals x) h k)

let evars x h k =
  PrintOpt.enforce h (fun () -> eval_call (Serialize.evars x) h k)
