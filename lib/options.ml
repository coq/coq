(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util

let boot = ref false

let batch_mode = ref false

let debug = ref false

let print_emacs = ref false

let emacs_str s = if !print_emacs then s else "" 

let term_quality = ref false

(* Silent / Verbose *)
let silent = ref false
let make_silent flag = silent := flag; ()
let is_silent () = !silent
let is_verbose () = not !silent

let silently f x =
  let oldsilent = !silent in
  try 
    silent := true;
    let rslt = f x in
    silent := oldsilent; 
    rslt
  with e -> begin
    silent := oldsilent; raise e
  end

let if_silent f x = if !silent then f x
let if_verbose f x = if not !silent then f x

(* The number of printed hypothesis in a goal *)

let print_hyps_limit = ref (None : int option)
let set_print_hyps_limit n = print_hyps_limit := n
let print_hyps_limit () = !print_hyps_limit

(* A list of the areas of the system where "unsafe" operation
 * has been requested *)
let unsafe_set = ref Stringset.empty
let add_unsafe s = unsafe_set := Stringset.add s !unsafe_set
let is_unsafe s = Stringset.mem s !unsafe_set


(* Dump of globalization (to be used by coqdoc) *)

let dump = ref false
let dump_file = ref ""
let dump_into_file f = dump := true; dump_file := f

let dump_buffer = Buffer.create 8192

let dump_string = Buffer.add_string dump_buffer

let dump_it () = 
  if !dump then begin
    let mode = [Open_wronly; Open_append; Open_creat] in
    let c = open_out_gen mode 0o666 !dump_file in
    output_string c (Buffer.contents dump_buffer);
    close_out c
  end

let _ = at_exit dump_it
