(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Ideutils

(** * Version and date *)

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

let filter_coq_opts args =
  let argstr = String.concat " " (List.map Filename.quote args) in
  let cmd = Filename.quote !Minilib.coqtop_path ^" -nois -filteropts " ^ argstr in
  let oc,ic,ec = Unix.open_process_full cmd (Unix.environment ()) in
  let filtered_args = read_all_lines oc in
  let message = read_all_lines ec in
  match Unix.close_process_full (oc,ic,ec) with
    | Unix.WEXITED 0 -> true,filtered_args
    | Unix.WEXITED 2 -> false,filtered_args
    | _ -> false,message

exception Coqtop_output of string list

let check_connection args =
  try
    let argstr = String.concat " " (List.map Filename.quote args) in
    let cmd = Filename.quote !Minilib.coqtop_path ^ " -batch " ^ argstr in
    let ic = Unix.open_process_in cmd in
    let lines = read_all_lines ic in
    match Unix.close_process_in ic with
    | Unix.WEXITED 0 -> prerr_endline "coqtop seems ok"
    | _ -> raise (Coqtop_output lines)
  with
    | End_of_file ->
      safe_prerr_endline "Cannot start connection with coqtop";
      exit 1
    | Coqtop_output lines ->
      safe_prerr_endline "Connection with coqtop failed:";
      List.iter safe_prerr_endline lines;
      exit 1

(** It is tempting to merge the following function with the previous one,
    but check_connection fails if no initial.coq is found, while
    check_coqlib doesn't check that. *)

let check_coqlib args =
  try
    let argstr = String.concat " " (List.map Filename.quote args) in
    let cmd = Filename.quote !Minilib.coqtop_path ^ " " ^ argstr ^ " -where" in
    let ic = Unix.open_process_in cmd in
    let lines = read_all_lines ic in
    match Unix.close_process_in ic with
    | Unix.WEXITED 0 ->
      (match lines with
	| [coqlib] -> coqlib
	| _ -> raise (Coqtop_output lines))
    | _ -> raise (Coqtop_output lines)
  with
    | End_of_file ->
      safe_prerr_endline "Cannot start connection with coqtop";
      exit 1
    | Coqtop_output lines ->
      safe_prerr_endline "Connection with coqtop failed:";
      List.iter safe_prerr_endline lines;
      exit 1


(** * The structure describing a coqtop sub-process *)

type coqtop = {
  pid : int; (* Unix process id *)
  cout : in_channel ;
  cin : out_channel ;
  sup_args : string list;
}

(** * Count of all active coqtops *)

let toplvl_ctr = ref 0

let toplvl_ctr_mtx = Mutex.create ()

let coqtop_zombies () =
  Mutex.lock toplvl_ctr_mtx;
  let res = !toplvl_ctr in
  Mutex.unlock toplvl_ctr_mtx;
  res


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

let spawn_coqtop sup_args =
  Mutex.lock toplvl_ctr_mtx;
  try
    let prog = !Minilib.coqtop_path in
    let args = Array.of_list (prog :: "-ideslave" :: sup_args) in
    let (pid,ic,oc) = open_process_pid prog args in
    incr toplvl_ctr;
    Mutex.unlock toplvl_ctr_mtx;
    { pid = pid; cin = oc; cout = ic ; sup_args = sup_args }
  with e ->
    Mutex.unlock toplvl_ctr_mtx;
    raise e

let respawn_coqtop coqtop = spawn_coqtop coqtop.sup_args

let break_coqtop coqtop =
  try Unix.kill coqtop.pid Sys.sigint
  with _ -> prerr_endline "Error while sending Ctrl-C"

let killer = ref (fun pid -> Unix.kill pid Sys.sigkill)

let kill_coqtop coqtop =
  let pid = coqtop.pid in
  begin
    try !killer pid
    with _ -> prerr_endline "Kill -9 failed. Process already terminated ?"
  end;
  try
    ignore (Unix.waitpid [] pid);
    Mutex.lock toplvl_ctr_mtx; decr toplvl_ctr; Mutex.unlock toplvl_ctr_mtx
  with _ -> prerr_endline "Error while waiting for child"

(** * Calls to coqtop *)

(** Cf [Ide_intf] for more details *)

let eval_call coqtop (c:'a Ide_intf.call) =
  Marshal.to_channel coqtop.cin c [];
  flush coqtop.cin;
  (Marshal.from_channel: in_channel -> 'a Ide_intf.value) coqtop.cout

let interp coqtop b s = eval_call coqtop (Ide_intf.interp (b,s))
let raw_interp coqtop s = eval_call coqtop (Ide_intf.raw_interp s)
let read_stdout coqtop = eval_call coqtop Ide_intf.read_stdout
let rewind coqtop i = eval_call coqtop (Ide_intf.rewind i)
let is_in_loadpath coqtop s = eval_call coqtop (Ide_intf.is_in_loadpath s)
let make_cases coqtop s = eval_call coqtop (Ide_intf.make_cases s)
let current_status coqtop = eval_call coqtop Ide_intf.current_status

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
    List.fold_left
      (fun acc cmd -> 
         let str = (if value then "Set" else "Unset") ^ " Printing " ^ cmd ^ "." in
         match raw_interp coqtop str with
           | Ide_intf.Good () -> acc
           | Ide_intf.Fail (l,errstr) ->  Ide_intf.Fail (l,"Could not eval \""^str^"\": "^errstr)
      )
      (Ide_intf.Good ())
      opt

  let enforce_hack coqtop = Hashtbl.fold
    (fun opt v acc ->
      match set coqtop opt v with
        | Ide_intf.Good () -> Ide_intf.Good ()
        | Ide_intf.Fail str -> Ide_intf.Fail str)
    state_hack (Ide_intf.Good ())
end

let current_goals coqtop =
  match PrintOpt.enforce_hack coqtop with
    | Ide_intf.Good () -> eval_call coqtop Ide_intf.current_goals
    | Ide_intf.Fail str -> Ide_intf.Fail str

