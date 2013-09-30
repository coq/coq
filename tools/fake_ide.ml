(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Fake_ide : Simulate a [coqide] talking to a [coqtop -ideslave] *)

exception Comment

type coqtop = {
  xml_printer : Xml_printer.t;
  xml_parser : Xml_parser.t;
}

let logger level content = ()

let base_eval_call call coqtop =
  prerr_endline (Serialize.pr_call call);
  let xml_query = Serialize.of_call call in
  Xml_printer.print coqtop.xml_printer xml_query;
  let rec loop () =
    let xml = Xml_parser.parse coqtop.xml_parser in
    if Serialize.is_message xml then
      let message = Serialize.to_message xml in
      let level = message.Interface.message_level in
      let content = message.Interface.message_content in
      let () = logger level content in
      loop ()
    else if Serialize.is_feedback xml then
      loop ()
    else (Serialize.to_answer call xml)
  in
  let res = loop () in
  prerr_endline (Serialize.pr_full_value call res);
  match res with Interface.Fail _ -> exit 1 | x -> x

let eval_call c q = ignore(base_eval_call c q)

let ids = ref []
let store_id = function
  | Interface.Fail _ -> ()
  | Interface.Good (id, _) -> ids := id :: !ids
let rec erase_ids n =
  if n = 0 then
    match !ids with
    | [] -> Stateid.initial
    | x :: _ -> x
  else match !ids with
    | id :: rest -> ids := rest; erase_ids (n-1)
    | [] -> exit 1
let eid = ref 0
let edit () = incr eid; !eid
let curid () = match !ids with x :: _ -> x | _ -> Stateid.initial

let commands =
  [ "INTERPRAWSILENT", (fun s -> eval_call (Serialize.query (s,Stateid.dummy)));
    "INTERPRAW", (fun s -> eval_call (Serialize.query (s,Stateid.dummy)));
    "INTERPSILENT", (fun s c ->
      store_id (base_eval_call (Serialize.add ((s,edit()),(curid(),false))) c));
    "INTERP", (fun s c ->
      store_id (base_eval_call (Serialize.add ((s,edit()),(curid(),true))) c));
    "REWIND", (fun s ->
      let i = int_of_string s in
      let id = erase_ids i in
      eval_call (Serialize.edit_at id));
    "GOALS", (fun _ -> eval_call (Serialize.goals ()));
    "HINTS", (fun _ -> eval_call (Serialize.hints ()));
    "GETOPTIONS", (fun _ -> eval_call (Serialize.get_options ()));
    "STATUS", (fun _ -> eval_call (Serialize.status false));
    "INLOADPATH", (fun s -> eval_call (Serialize.inloadpath s));
    "MKCASES", (fun s -> eval_call (Serialize.mkcases s));
    "#", (fun _ -> raise Comment);
  ]

let read_eval_print line =
  let lline = String.length line in
  let rec find_cmd = function
    | [] -> prerr_endline ("Error: Unknown API Command :"^line); exit 1
    | (cmd,fn) :: cmds ->
      let lcmd = String.length cmd in
      if lline >= lcmd && String.sub line 0 lcmd = cmd then
	let arg = try String.sub line (lcmd+1) (lline-lcmd-1) with _ -> ""
	in fn arg
      else find_cmd cmds
  in
  find_cmd commands

let usage () =
  Printf.printf
    "A fake coqide process talking to a coqtop -ideslave.\n\
     Usage: %s [<coqtop>]\n\
     Input syntax is one API call per line, the keyword coming first,\n\
     with the rest of the line as string argument (e.g. INTERP Check plus.)\n\
     Supported API keywords are:\n" (Filename.basename Sys.argv.(0));
  List.iter (fun (s,_) -> Printf.printf "\t%s\n" s) commands;
  exit 1

let main =
  Sys.set_signal Sys.sigpipe
    (Sys.Signal_handle
       (fun _ -> prerr_endline "Broken Pipe (coqtop died ?)"; exit 1));
  let coqtop_name = match Array.length Sys.argv with
    | 1 -> "coqtop"
    | 2 when Sys.argv.(1) <> "-help" -> Sys.argv.(1)
    | _ -> usage ()
  in
  let coqtop =
    let (cin, cout) = Unix.open_process (coqtop_name^" -ideslave") in
    let ip = Xml_parser.make (Xml_parser.SChannel cin) in
    let op = Xml_printer.make (Xml_printer.TChannel cout) in
    let () = Xml_parser.check_eof ip false in
    {
      xml_printer = op;
      xml_parser = ip;
    }
  in
  while true do
    let l = try read_line () with End_of_file -> exit 0
    in
    try read_eval_print l coqtop
    with
      | Comment -> ()
      | e ->
	prerr_endline ("Uncaught exception" ^ Printexc.to_string e); exit 1
  done
