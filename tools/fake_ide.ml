(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Fake_ide : Simulate a [coqide] talking to a [coqtop -ideslave] *)

exception Comment

let coqtop = ref (stdin, stdout)

let p = Xml_parser.make ()
let () = Xml_parser.check_eof p false

let eval_call (call:'a Ide_intf.call) =
  prerr_endline (Ide_intf.pr_call call);
  let xml_query = Ide_intf.of_call call in
  Xml_utils.print_xml (snd !coqtop) xml_query;
  flush (snd !coqtop);
  let xml_answer = Xml_parser.parse p (Xml_parser.SChannel (fst !coqtop)) in
  let res = Ide_intf.to_answer xml_answer in
  prerr_endline (Ide_intf.pr_full_value call res);
  match res with Interface.Fail _ -> exit 1 | _ -> ()

let commands =
  [ "INTERPRAWSILENT", (fun s -> eval_call (Ide_intf.interp (true,false,s)));
    "INTERPRAW", (fun s -> eval_call (Ide_intf.interp (true,true,s)));
    "INTERPSILENT", (fun s -> eval_call (Ide_intf.interp (false,false,s)));
    "INTERP", (fun s -> eval_call (Ide_intf.interp (false,true,s)));
    "REWIND", (fun s -> eval_call (Ide_intf.rewind (int_of_string s)));
    "GOALS", (fun _ -> eval_call Ide_intf.goals);
    "STATUS", (fun _ -> eval_call Ide_intf.status);
    "INLOADPATH", (fun s -> eval_call (Ide_intf.inloadpath s));
    "MKCASES", (fun s -> eval_call (Ide_intf.mkcases s));
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
  coqtop := Unix.open_process (coqtop_name^" -ideslave");
  while true do
    let l = try read_line () with End_of_file -> exit 0
    in
    try read_eval_print l
    with
      | Comment -> ()
      | e ->
	prerr_endline ("Uncaught exception" ^ Printexc.to_string e); exit 1
  done
