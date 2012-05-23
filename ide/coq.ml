(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
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

let atomically mtx f arg =
  Mutex.lock mtx;
  try
    let ans = f arg in
    Mutex.unlock mtx;
    ans
  with err ->
    Mutex.unlock mtx;
    raise err

let ignore_error f arg =
  try ignore (f arg) with _ -> ()

(** * The structure describing a coqtop sub-process *)

type handle = {
  pid : int;
  (* Unix process id *)
  cout : in_channel;
  cin : out_channel;
  mutable alive : bool;
}

type coqtop = {
  (* lock managing coqtop access *)
  lock : Mutex.t;
  (* non quoted command-line arguments of coqtop *)
  sup_args : string list;
  (* actual coqtop process *)
  mutable handle : handle;
  (* trigger called whenever coqtop dies abruptly *)
  trigger : handle -> unit;
  (* whether coqtop may be relaunched *)
  mutable is_closed : bool;
  (* whether coqtop is computing *)
  mutable is_computing : bool;
  (* whether coqtop is waiting to be resetted *)
  mutable is_to_reset : bool;
}

(** Invariants:
  - any outside request takes the coqtop.lock and is discarded when
    [is_closed = true].
  - coqtop.handle may be written ONLY when toplvl_ctr_mtx AND coqtop.lock is 
    taken.
*)

exception DeadCoqtop

(** * Count of all active coqtops *)

let toplvl_ctr = ref 0

let toplvl_ctr_mtx = Mutex.create ()

let coqtop_zombies () = !toplvl_ctr

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
*)

let open_process_pid prog args =
  let (ide2top_r,ide2top_w) = Unix.pipe () in
  let (top2ide_r,top2ide_w) = Unix.pipe () in
  let pid = Unix.create_process prog args ide2top_r top2ide_w Unix.stderr in
  assert (pid <> 0);
  Unix.close ide2top_r;
  Unix.close top2ide_w;
  let oc = Unix.out_channel_of_descr ide2top_w in
  let ic = Unix.in_channel_of_descr top2ide_r in
  set_binary_mode_out oc true;
  set_binary_mode_in ic true;
  (pid,ic,oc)

(** This launches a fresh handle from its command line arguments. *)
let unsafe_spawn_handle args =
  let prog = coqtop_path () in
  let args = Array.of_list (prog :: "-ideslave" :: args) in
  let (pid, ic, oc) = open_process_pid prog args in
  incr toplvl_ctr;
  {
    pid = pid;
    cin = oc;
    cout = ic;
    alive = true;
  }

(** This clears any potentially remaining open garbage. *)
let unsafe_clear_handle coqtop =
  let handle = coqtop.handle in
  if handle.alive then begin
    (* invalidate the old handle *)
    handle.alive <- false;
    ignore_error close_out handle.cin;
    ignore_error close_in handle.cout;
    ignore_error (Unix.waitpid []) handle.pid;
    decr toplvl_ctr
  end

let spawn_coqtop hook sup_args =
  let handle =
    atomically toplvl_ctr_mtx unsafe_spawn_handle sup_args
  in
  {
    handle = handle;
    lock = Mutex.create ();
    sup_args = sup_args;
    trigger = hook;
    is_closed = false;
    is_computing = false;
    is_to_reset = false;
  }

let interrupter = ref (fun pid -> Unix.kill pid Sys.sigint)
let killer = ref (fun pid -> Unix.kill pid Sys.sigkill)

let is_computing coqtop = coqtop.is_computing

let is_closed coqtop = coqtop.is_closed

(** These are asynchronous signals *)
let break_coqtop coqtop =
  try !interrupter coqtop.handle.pid
  with _ -> Minilib.log "Error while sending Ctrl-C"

let kill_coqtop coqtop =
  try !killer coqtop.handle.pid
  with _ -> Minilib.log "Kill -9 failed. Process already terminated ?"

let unsafe_process coqtop f =
  coqtop.is_computing <- true;
  try
    f coqtop.handle;
    coqtop.is_computing <- false;
    Mutex.unlock coqtop.lock
  with
  | DeadCoqtop ->
    coqtop.is_computing <- false;
    Mutex.lock toplvl_ctr_mtx;
    (* Coqtop died from an non natural cause, we have the lock, so it's our duty 
       to relaunch it here. *)
    if not coqtop.is_closed && not coqtop.is_to_reset then begin
      ignore_error unsafe_clear_handle coqtop;
      let try_respawn () =
      coqtop.handle <- unsafe_spawn_handle coqtop.sup_args;
      in
      ignore_error try_respawn ();
      (* If respawning coqtop failed, there is not much we can do... *)
      assert (coqtop.handle.alive = true);
      (* Process the reset callback *)
      ignore_error coqtop.trigger coqtop.handle;
    end;
    Mutex.unlock toplvl_ctr_mtx;
    Mutex.unlock coqtop.lock;
  | err ->
    (* Another error occured, we propagate it. *)
    coqtop.is_computing <- false;
    Mutex.unlock coqtop.lock;
    raise err

let grab coqtop f =
  Mutex.lock coqtop.lock;
  if not coqtop.is_closed && not coqtop.is_to_reset then unsafe_process coqtop f
  else Mutex.unlock coqtop.lock

let try_grab coqtop f g =
  if Mutex.try_lock coqtop.lock then
    if not coqtop.is_closed && not coqtop.is_to_reset then unsafe_process coqtop f
    else Mutex.unlock coqtop.lock
  else g ()

(** * Calls to coqtop *)

(** Cf [Ide_intf] for more details *)

let p = Xml_parser.make ()
let () = Xml_parser.check_eof p false

let eval_call coqtop (c:'a Serialize.call) =
  try
    Xml_utils.print_xml coqtop.cin (Serialize.of_call c);
    flush coqtop.cin;
    let xml = Xml_parser.parse p (Xml_parser.SChannel coqtop.cout) in
    (Serialize.to_answer xml : 'a Interface.value)
  with
  | Serialize.Marshal_error ->
    (* the protocol was not respected... *)
    raise Serialize.Marshal_error
  | err ->
    (* if anything else happens here, coqtop is most likely dead *)
    let msg = Printf.sprintf "Error communicating with pid [%i]: %s"
      coqtop.pid (Printexc.to_string err)
    in
    Minilib.log msg;
    raise DeadCoqtop

let interp coqtop ?(raw=false) ?(verbose=true) s =
  eval_call coqtop (Serialize.interp (raw,verbose,s))
let rewind coqtop i = eval_call coqtop (Serialize.rewind i)
let inloadpath coqtop s = eval_call coqtop (Serialize.inloadpath s)
let mkcases coqtop s = eval_call coqtop (Serialize.mkcases s)
let status coqtop = eval_call coqtop Serialize.status
let hints coqtop = eval_call coqtop Serialize.hints
let search coqtop flags = eval_call coqtop (Serialize.search flags)

let unsafe_close coqtop =
  if Mutex.try_lock coqtop.lock then begin
    let () =
      try
        match eval_call coqtop.handle Serialize.quit with
        | Interface.Good _ -> ()
        | _ -> raise Exit
      with err -> kill_coqtop coqtop
    in
    Mutex.unlock coqtop.lock
  end else begin
    (* bring me the chainsaw! *)
    kill_coqtop coqtop
  end

let close_coqtop coqtop =
  (* wait for acquiring the process management lock *)
  atomically toplvl_ctr_mtx (fun _ -> coqtop.is_closed <- true) ();
  (* try to quit coqtop gently *)
  unsafe_close coqtop;
  (* Finalize the handle *)
  Mutex.lock coqtop.lock;
  Mutex.lock toplvl_ctr_mtx;
    ignore_error unsafe_clear_handle coqtop;
  Mutex.unlock toplvl_ctr_mtx;
  Mutex.unlock coqtop.lock

let reset_coqtop coqtop hook =
  (* wait for acquiring the process management lock *)
  atomically toplvl_ctr_mtx (fun _ -> coqtop.is_to_reset <- true) ();
  (* try to quit coqtop gently *)
  unsafe_close coqtop;
  (* Reset the handle *)
  Mutex.lock coqtop.lock;
  Mutex.lock toplvl_ctr_mtx;
    ignore_error unsafe_clear_handle coqtop;
    let try_respawn () =
    coqtop.handle <- unsafe_spawn_handle coqtop.sup_args;
    in
    ignore_error try_respawn ();
    (* If respawning coqtop failed, there is not much we can do... *)
    assert (coqtop.handle.alive = true);
    (* Reset done *)
    coqtop.is_to_reset <- false;
    (* Process the reset callback with the given hook *)
    ignore_error hook coqtop.handle;
  Mutex.unlock toplvl_ctr_mtx;
  Mutex.unlock coqtop.lock

module PrintOpt =
struct
  type t = string list
  let implicit = ["Printing"; "Implicit"]
  let coercions = ["Printing"; "Coercions"]
  let raw_matching = ["Printing"; "Matching"; "Synth"]
  let notations = ["Printing"; "Notations"]
  let all_basic = ["Printing"; "All"]
  let existential = ["Printing"; "Existential"; "Instances"]
  let universes = ["Printing"; "Universes"]

  let state_hack = Hashtbl.create 11
  let _ = List.iter (fun opt -> Hashtbl.add state_hack opt false)
            [ implicit; coercions; raw_matching; notations; all_basic; existential; universes ]

  let set coqtop options =
    let () = List.iter (fun (name, v) -> Hashtbl.replace state_hack name v) options in
    let options = List.map (fun (name, v) -> (name, Interface.BoolValue v)) options in
    match eval_call coqtop (Serialize.set_options options) with
    | Interface.Good () -> ()
    | _ -> raise (Failure "Cannot set options.")

  let enforce_hack coqtop =
    let elements = Hashtbl.fold (fun opt v acc -> (opt, v) :: acc) state_hack [] in
    set coqtop elements

end

let goals coqtop =
  let () = PrintOpt.enforce_hack coqtop in
  eval_call coqtop Serialize.goals

let evars coqtop =
  let () = PrintOpt.enforce_hack coqtop in
  eval_call coqtop Serialize.evars
