(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(* usage: get_files <regexp>

read from stdin
print on stdout all (non-overlapping) sub-strings matching <regexp> *)

open Str

let main() =
  if Array.length Sys.argv <> 2 then
    (prerr_endline ("usage: " ^ Sys.argv.(0) ^ " <regexp>"); exit 1);
  let re = regexp Sys.argv.(1) in
  try
    while true do
      let s = read_line() in
	try
	  let p = ref 0 in
	    while true do
	      p := 1 + (search_forward re s !p);
	      print_string ((matched_string s) ^ " ")
	    done
	with Not_found -> ()
    done
  with End_of_file -> print_newline()

let _ = main()
