(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Compat
open Pp
open Ideutils

type coqtop = {
  mutable pid : int;
  mutable cout : in_channel ;
  mutable cin : out_channel ;
  sup_args : string list;
  mutable version : int ;
}

let prerr_endline s = if !debug then prerr_endline s else ()

let output = ref (Format.formatter_of_out_channel stdout)

let msg m =
  let b =  Buffer.create 103 in
  Pp.msg_with (Format.formatter_of_buffer b) m;
  Buffer.contents b

let msgnl m =
  (msg m)^"\n"

let i = ref 0

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

let rec read_all_lines in_chan =
  try
    let arg = input_line in_chan in
    arg::(read_all_lines in_chan)
  with End_of_file -> []

let coqtop_path () =
  let prog = Sys.executable_name in
  let dir = Filename.dirname prog in
  if Filename.check_suffix prog ".byte" then dir^"/coqtop.byte"
  else dir^"/coqtop.opt"

let filter_coq_opts args =
  let argstr = String.concat " " (List.map Filename.quote args) in
  let oc,ic,ec = Unix.open_process_full (coqtop_path () ^" -nois -filteropts "^argstr) (Unix.environment ()) in
  let filtered_args = read_all_lines oc in
  let message = read_all_lines ec in
  match Unix.close_process_full (oc,ic,ec) with
    | Unix.WEXITED 0 -> true,filtered_args
    | Unix.WEXITED 2 -> false,filtered_args
    | _ -> false,message

exception Coqtop_output of string list

let check_connection args =
  try
    let args = String.concat " " ("-batch"::args) in
    let ic = Unix.open_process_in (coqtop_path () ^ " " ^ args) in
    let lines = read_all_lines ic in
    match (Unix.close_process_in ic) with
    | Unix.WEXITED 0 -> prerr_endline "coqtop seems ok"
    | _ -> raise (Coqtop_output lines)
  with End_of_file ->
    Pervasives.prerr_endline "Cannot start connection with coqtop";
    | Coqtop_output lines ->
      Pervasives.prerr_endline "Connection with coqtop failed:";
      List.iter Pervasives.prerr_endline lines;
      exit 1

let eval_call coqtop (c:'a Ide_intf.call) =
  Marshal.to_channel coqtop.cin c [];
  flush coqtop.cin;
  (Marshal.from_channel: in_channel -> 'a Ide_intf.value) coqtop.cout

let is_in_loadpath coqtop s = eval_call coqtop (Ide_intf.is_in_loadpath s)
 
let raw_interp coqtop s = eval_call coqtop (Ide_intf.raw_interp s)

let interp coqtop b s = eval_call coqtop (Ide_intf.interp b s)

let rewind coqtop i = eval_call coqtop (Ide_intf.rewind i)
 
let read_stdout coqtop = eval_call coqtop Ide_intf.read_stdout

let toplvl_ctr = ref 0

let toplvl_ctr_mtx = Mutex.create ()

let spawn_coqtop sup_args =
  Mutex.lock toplvl_ctr_mtx;
  try
    let (in_read,in_write) = Unix.pipe () in
    let (out_read,out_write) = Unix.pipe () in
    let prog = coqtop_path () in
    let args = Array.of_list (prog :: "-ideslave" :: sup_args) in
    let pid = Unix.create_process prog args out_read in_write Unix.stderr in
    assert (pid <> 0);
    Unix.close out_read;
    Unix.close in_write;
    let ic = Unix.in_channel_of_descr in_read in
    let oc = Unix.out_channel_of_descr out_write in
    set_binary_mode_out oc true;
    set_binary_mode_in ic true;
    incr toplvl_ctr;
    Mutex.unlock toplvl_ctr_mtx;
    { pid = pid; cin = oc; cout = ic ; sup_args = sup_args ; version = 0 }
  with e ->
    Mutex.unlock toplvl_ctr_mtx;
    raise e

let break_coqtop coqtop =
  try Unix.kill coqtop.pid Sys.sigint
  with _ -> prerr_endline "Error while sending Ctrl-C"

let blocking_kill pid =
  begin
    try Unix.kill pid Sys.sigkill;
    with _ -> prerr_endline "Kill -9 failed. Process already terminated ?"
  end;
  try
    ignore (Unix.waitpid [] pid);
    Mutex.lock toplvl_ctr_mtx; decr toplvl_ctr; Mutex.unlock toplvl_ctr_mtx
  with _ -> prerr_endline "Error while waiting for child"

let kill_coqtop coqtop =
  ignore (Thread.create blocking_kill coqtop.pid)

let coqtop_zombies =
  (fun () ->
     Mutex.lock toplvl_ctr_mtx;
     let res = !toplvl_ctr in
     Mutex.unlock toplvl_ctr_mtx;
     res)

let reset_coqtop coqtop =
  kill_coqtop coqtop;
  let ni = spawn_coqtop coqtop.sup_args in
  coqtop.cin <- ni.cin;
  coqtop.cout <- ni.cout;
  coqtop.pid <- ni.pid

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

let process_exn = function
  | End_of_file ->
    "Warning: End_of_file occurred (possibly a forced restart of coqtop)", None
  | e -> Printexc.to_string e,None

let goals coqtop =
  match PrintOpt.enforce_hack coqtop with
    | Ide_intf.Good () -> eval_call coqtop Ide_intf.current_goals
    | Ide_intf.Fail str -> Ide_intf.Fail str

let make_cases coqtop s = eval_call coqtop (Ide_intf.make_cases s)

let current_status coqtop = eval_call coqtop Ide_intf.current_status
