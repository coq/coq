(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Util

let with_option o f x =
  let old = !o in o:=true;
  try let r = f x in o := old; r
  with e -> o := old; raise e

let boot = ref false

let batch_mode = ref false

let debug = ref false

let print_emacs = ref false
let print_emacs_safechar = ref false

let term_quality = ref false

let xml_export = ref false

let dont_load_proofs = ref false

let raw_print = ref false

let unicode_syntax = ref false

(* Translate *)
let translate = ref false
let make_translate f = translate := f
let do_translate () = !translate
let translate_file = ref false

(* True only when interning from pp*new.ml *)
let translate_syntax = ref false

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

let hash_cons_proofs = ref true

let warn = ref true
let make_warn flag = warn := flag;  ()
let if_warn f x = if !warn then f x

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

(* Flags.for the virtual machine *)

let boxed_definitions = ref true
let set_boxed_definitions b = boxed_definitions := b
let boxed_definitions _ = !boxed_definitions 
 
(* Flags.for external tools *)

let subst_command_placeholder s t =
  let buff = Buffer.create (String.length s + String.length t) in
  for i = 0 to String.length s - 2 do
    if s.[i] = '%' & s.[i+1] = 's' then Buffer.add_string buff t
    else Buffer.add_char buff s.[i]
  done;
  Buffer.contents buff

let browser_cmd_fmt =
 try
  let coq_netscape_remote_var = "COQREMOTEBROWSER" in
  Sys.getenv coq_netscape_remote_var
 with
  Not_found ->
   if Sys.os_type = "Win32"
   then "C:\\PROGRA~1\\INTERN~1\\IEXPLORE %s"
   else "firefox -remote \"OpenURL(%s,new-tab)\" || firefox %s"
