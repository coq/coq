(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ideutils
open Preferences

let ideslave_coqtop_flags = ref None

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
      if len > 0 && arg.[len - 1] = '\r' then
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
      let () = cmd_coqtop#set None in
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
    let oc,ic,ec = Unix.open_process_full cmd (Unix.environment ()) in
    lines := read_all_lines oc @ read_all_lines ec;
    match Unix.close_process_full (oc,ic,ec) with
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

type 'a poly_ccb = 'a Xmlprotocol.call * ('a Interface.value -> void)
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
end

module CoqTop = Spawn.Async(GlibMainLoop)

type handle = {
  proc : CoqTop.process;
  xml_oc : Xml_printer.t;
  mutable alive : bool;
  mutable waiting_for : ccb option; (* last call + callback *)
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
  mutable reset_handler : unit task;
  (* called whenever coqtop sends a feedback message *)
  mutable feedback_handler : Feedback.feedback -> unit;
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

let handle_feedback feedback_processor xml =
  let feedback = Xmlprotocol.to_feedback xml in
  feedback_processor feedback

let handle_final_answer handle xml =
  let () = Minilib.log "Handling coqtop answer" in
  let ccb = match handle.waiting_for with
    | None -> raise (AnswerWithoutRequest (Xml_printer.to_string_fmt xml))
    | Some c -> c in
  let () = handle.waiting_for <- None in
  with_ccb ccb { bind_ccb = fun (c, f) -> f (Xmlprotocol.to_answer c xml) }

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
    let xml = Xml_parser.parse ~do_not_canonicalize:true p in
    let l_end = Lexing.lexeme_end lex in
    state.fragment <- String.sub s l_end (String.length s - l_end);
    state.lexerror <- None;
    if Xmlprotocol.is_feedback xml then begin
      handle_feedback feedback_processor xml;
      loop ()
    end else
      begin
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
  | Serialize.Marshal_error(expected,actual) ->
      "Protocol violation. Expected: " ^ expected ^ " Actual: "
        ^ Xml_printer.to_string actual
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
  let async_default =
    (* disable async processing by default in Windows *)
    if List.mem Sys.os_type ["Win32"; "Cygwin"] then
      "off"
    else
      "on"
  in
  let args = Array.of_list ("--xml_format=Ppcmds" :: "-async-proofs" :: async_default :: args) in
  let env =
    match !ideslave_coqtop_flags with
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

let save_all = ref (fun () -> assert false)

let rec respawn_coqtop ?(why=Unexpected) coqtop =
  let () = match why with
  | Unexpected ->
    let title = "Warning" in
    let icon = (warn_image ())#coerce in
    let buttons = ["Reset"; "Save all and quit"; "Quit without saving"] in
    let ans = GToolbox.question_box ~title ~buttons ~icon "Coqtop died badly." in
    if ans = 2 then (!save_all (); GtkMain.Main.quit ())
    else if ans = 3 then GtkMain.Main.quit ()
  | Planned -> ()
  in
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
  ignore (coqtop.reset_handler coqtop.handle (mkready coqtop))

let spawn_coqtop sup_args =
  bind_self_as (fun this -> {
    handle = spawn_handle sup_args
               (fun () -> respawn_coqtop (this ()))
               (fun msg -> (this ()).feedback_handler msg);
    sup_args = sup_args;
    reset_handler = (fun _ k -> k ());
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

let eval_call call handle k =
  (** Send messages to coqtop and prepare the decoding of the answer *)
  Minilib.log ("Start eval_call " ^ Xmlprotocol.pr_call call);
  assert (handle.alive && handle.waiting_for = None);
  handle.waiting_for <- Some (mk_ccb (call,k));
  Xml_printer.print handle.xml_oc (Xmlprotocol.of_call call);
  Minilib.log "End eval_call";
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

let break_coqtop coqtop workers =
  if coqtop.status = Busy then
    try !interrupter (CoqTop.unixpid coqtop.handle.proc)
    with _ -> Minilib.log "Error while sending Ctrl-C"
  else
    let rec aux = function
    | [] -> Void
    | w :: ws -> stop_worker w coqtop.handle (fun _ -> aux ws)
    in
      let Void = aux workers in ()

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
  let raw_matching = BoolOpt ["Printing"; "Matching"]
  let notations = BoolOpt ["Printing"; "Notations"]
  let all_basic = BoolOpt ["Printing"; "All"]
  let existential = BoolOpt ["Printing"; "Existential"; "Instances"]
  let universes = BoolOpt ["Printing"; "Universes"]
  let unfocused = BoolOpt ["Printing"; "Unfocused"]
  let diff = StringOpt ["Diffs"]

  type 'a descr = { opts : 'a t list; init : 'a; label : string }

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
      label = "Display all _low-level contents" };
    { opts = [unfocused]; init = false; label = "Display _unfocused goals" }
  ]

  let diff_item = { opts = [diff]; init = "off"; label = "Display _proof diffs" }

  (** The current status of the boolean options *)

  let current_state = Hashtbl.create 11

  let set (type a) (opt : a t) (v : a) =
    Hashtbl.replace current_state (opt_name opt) (opt_data opt v)

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

  (** Transmitting options to coqtop *)

  let enforce h k =
    let mkopt o v acc = (o, v) :: acc in
    let opts = Hashtbl.fold mkopt current_state [] in
    eval_call (Xmlprotocol.set_options opts) h
      (function
	| Interface.Good () -> k ()
	| _ -> failwith "Cannot set options. Resetting coqtop")

end

let goals x h k =
  PrintOpt.enforce h (fun () -> eval_call (Xmlprotocol.goals x) h k)

let evars x h k =
  PrintOpt.enforce h (fun () -> eval_call (Xmlprotocol.evars x) h k)
