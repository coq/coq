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
      | Unix.WEXITED 0 ->
	List.iter check_remaining_opt !filtered_args; !filtered_args
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
let soft_killer = ref (fun pid -> Unix.kill pid Sys.sigterm)
let killer = ref (fun pid -> Unix.kill pid Sys.sigkill)

(** Handling old processes *)

type unix_process_id = int
type retry = int

let zombies = ref ([] : (unix_process_id * retry) list)

let pr_zombies ?(full=false) l =
  let pr (pid,retries) =
    string_of_int pid ^
    if full then "["^string_of_int retries^"]" else ""
  in
  String.concat ", " (List.map pr l)

let is_buried pid =
  try fst (Unix.waitpid [Unix.WNOHANG] pid) <> 0
  with Unix.Unix_error _ -> false

let max_retry = 3 (* one soft then two hard kill attempts *)

let countdown = ref None
let final_countdown () = (countdown := Some max_retry)

let check_zombies () =
  (* First, do [waitpid] on our zombies and try to kill the survivors *)
  let handle_zombie others (pid,retries) =
    if is_buried pid then others
    else
      let () = match retries with
	| 0 -> () (* freshly closed coqtop, leave it some time *)
	| 1 -> ignore_error !soft_killer pid
	| _ -> ignore_error !killer pid
      in (pid,retries+1) :: others
  in
  let zs = List.fold_left handle_zombie [] !zombies
  in
  if zs <> [] then
    Minilib.log ("Remaining zombies: "^ pr_zombies ~full:true zs);
  (* Second, we warn the user about old zombies that refuses to die
     (except in the middle of the final countdown) *)
  let chk_old = !countdown = None || !countdown = Some 0 in
  let old_zombies, new_zombies =
    List.partition (fun (_,n) -> chk_old && n >= max_retry) zs
  in
  if old_zombies <> [] then begin
    let msg1 = "Some coqtop processes are still running.\n" in
    let msg2 = "You may have to kill them manually.\nPids: " in
    let msg3 = pr_zombies old_zombies in
    let popup = GWindow.message_dialog ~buttons:GWindow.Buttons.close
      ~message_type:`ERROR ~message:(msg1 ^ msg2 ^ msg3) ()
    in
    ignore (popup#run ());
    ignore (popup#destroy ())
  end;
  zombies := new_zombies;
  (* Finally, we might end coqide if the final countdown has started *)
  if !countdown = Some 0 || (!countdown <> None && zs = []) then exit 0;
  countdown := Option.map pred !countdown;
  true

let _ = Glib.Timeout.add ~ms:300 ~callback:check_zombies

(** * The structure describing a coqtop sub-process *)

type handle = {
  pid : unix_process_id;
  cout : Unix.file_descr;
  cin : out_channel;
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

type task = handle -> (unit -> void) -> void

type reset_kind = Planned | Unexpected

type coqtop = {
  (* non quoted command-line arguments of coqtop *)
  sup_args : string list;
  (* called whenever coqtop dies *)
  mutable reset_handler : reset_kind -> task;
  (* actual coqtop process and its status *)
  mutable handle : handle;
  mutable status : status;
}

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

let open_process_pid prog args =
  let (ide2top_r,ide2top_w) = Unix.pipe () in
  let (top2ide_r,top2ide_w) = Unix.pipe () in
  Unix.set_close_on_exec ide2top_w;
  Unix.set_close_on_exec top2ide_r;
  let pid = Unix.create_process prog args ide2top_r top2ide_w Unix.stderr in
  assert (pid <> 0);
  Unix.close ide2top_r;
  Unix.close top2ide_w;
  (pid,top2ide_r,Unix.out_channel_of_descr ide2top_w)

exception TubeError
exception AnswerWithoutRequest

let install_input_watch handle respawner =
  let io_chan = Glib.Io.channel_of_descr handle.cout in
  let all_conds = [`ERR; `HUP; `IN; `NVAL; `PRI] in (* all except `OUT *)
  let rec check_errors = function
    | [] -> ()
    | (`IN | `PRI) :: conds -> check_errors conds
    | e :: _ -> raise TubeError
  in
  let handle_intermediate_message logger xml =
    let message = Serialize.to_message xml in
    let level = message.Interface.message_level in
    let content = message.Interface.message_content in
    logger level content
  in
  let handle_final_answer ccb xml =
    Minilib.log "Handling coqtop answer";
    handle.waiting_for <- None;
    with_ccb ccb { bind_ccb = fun (c,f) -> f (Serialize.to_answer xml c) }
  in
  let unsafe_handle_input conds =
    check_errors conds;
    let s = io_read_all io_chan in
    if s = "" then raise TubeError;
    match handle.waiting_for with
      |None -> raise AnswerWithoutRequest
      |Some (ccb,logger) ->
	let p = Xml_parser.make (Xml_parser.SString s) in
	let rec loop () =
	  let xml = Xml_parser.parse p in
	  if Serialize.is_message xml then
	    (handle_intermediate_message logger xml; loop ())
	  else
	    ignore (handle_final_answer ccb xml)
	in
	try loop ()
	with Xml_parser.Error (Xml_parser.Empty, _) -> () (* end of s *)
  in
  let print_exception = function
    | Xml_parser.Error e -> Xml_parser.error e
    | Serialize.Marshal_error -> "Protocol violation"
    | e -> Printexc.to_string e
  in
  let handle_input conds =
    if not handle.alive then false (* coqtop already terminated *)
    else
      try unsafe_handle_input conds; true
      with e ->
	Minilib.log ("Coqtop reader failed, resetting: "^print_exception e);
	respawner ();
	false
  in
  ignore (Glib.Io.add_watch ~cond:all_conds ~callback:handle_input io_chan)

(** This launches a fresh handle from its command line arguments. *)
let spawn_handle args =
  let prog = coqtop_path () in
  let args = Array.of_list (prog :: "-ideslave" :: args) in
  let (pid, in_fd, oc) = open_process_pid prog args in
  {
    pid = pid;
    cin = oc;
    cout = in_fd;
    alive = true;
    waiting_for = None;
  }

(** This clears any potentially remaining open garbage. *)
let clear_handle h =
  if h.alive then begin
    (* invalidate the old handle *)
    h.alive <- false;
    ignore_error close_out h.cin;
    ignore_error Unix.close h.cout;
    (* we monitor the death of the old process *)
    zombies := (h.pid,0) :: !zombies
  end

let mkready coqtop =
  fun () -> coqtop.status <- Ready; Void

let rec respawn_coqtop ?(why=Unexpected) coqtop =
  clear_handle coqtop.handle;
  ignore_error (fun () -> coqtop.handle <- spawn_handle coqtop.sup_args) ();
  (* Normally, the handle is now a fresh one.
     If not, there isn't much we can do ... *)
  assert (coqtop.handle.alive = true);
  coqtop.status <- New;
  install_input_watch coqtop.handle (fun () -> respawn_coqtop coqtop);
  ignore (coqtop.reset_handler why coqtop.handle (mkready coqtop))

let spawn_coqtop sup_args =
  let ct =
  {
    handle = spawn_handle sup_args;
    sup_args = sup_args;
    reset_handler = (fun _ _ k -> k ());
    status = New;
  }
  in
  install_input_watch ct.handle (fun () -> respawn_coqtop ct);
  ct

let set_reset_handler coqtop hook = coqtop.reset_handler <- hook

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
  try !interrupter coqtop.handle.pid
  with _ -> Minilib.log "Error while sending Ctrl-C"

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

type 'a atask = handle -> ('a Interface.value -> void) -> void

let eval_call ?(logger=default_logger) call handle k =
  (** Send messages to coqtop and prepare the decoding of the answer *)
  Minilib.log ("Start eval_call " ^ Serialize.pr_call call);
  assert (handle.alive && handle.waiting_for = None);
  handle.waiting_for <- Some (mk_ccb (call,k), logger);
  Xml_utils.print_xml handle.cin (Serialize.of_call call);
  flush handle.cin;
  Minilib.log "End eval_call";
  Void

let interp ?(logger=default_logger) ?(raw=false) ?(verbose=true) s =
  eval_call ~logger (Serialize.interp (raw,verbose,s))
let rewind i = eval_call (Serialize.rewind i)
let inloadpath s = eval_call (Serialize.inloadpath s)
let mkcases s = eval_call (Serialize.mkcases s)
let status = eval_call Serialize.status
let hints = eval_call Serialize.hints
let search flags = eval_call (Serialize.search flags)

module PrintOpt =
struct
  type t = string list

  let width_ref = ref None
  let set_printing_width w = width_ref := Some w

  let width = ["Printing"; "Width"]
  let implicit = ["Printing"; "Implicit"]
  let coercions = ["Printing"; "Coercions"]
  let raw_matching = ["Printing"; "Matching"]
  let notations = ["Printing"; "Notations"]
  let all_basic = ["Printing"; "All"]
  let existential = ["Printing"; "Existential"; "Instances"]
  let universes = ["Printing"; "Universes"]

  let state_hack = Hashtbl.create 11
  let _ = List.iter (fun opt -> Hashtbl.add state_hack opt false)
            [ implicit; coercions; raw_matching; notations;
	      all_basic; existential; universes ]

  let set opts h k =
    List.iter (fun (name, v) -> Hashtbl.replace state_hack name v) opts;
    let opts = List.map (fun (n, v) -> (n, Interface.BoolValue v)) opts in
    let opts = (width, Interface.IntValue !width_ref):: opts in
    eval_call (Serialize.set_options opts) h
      (function
	| Interface.Good () -> k ()
	| _ -> failwith "Cannot set options. Resetting coqtop")

  let enforce_hack h k =
    let elements = Hashtbl.fold (fun opt v acc -> (opt, v) :: acc) state_hack []
    in
    set elements h k

end

let goals h k =
  PrintOpt.enforce_hack h (fun () -> eval_call Serialize.goals h k)

let evars h k =
  PrintOpt.enforce_hack h (fun () -> eval_call Serialize.evars h k)
