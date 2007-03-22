(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)



(*s Output options *)

type target_language = LaTeX | HTML | TeXmacs

let target_language = ref HTML

type output_t =
  | StdOut
  | MultFiles
  | File of string

let output_dir = ref ""

let out_to = ref MultFiles

let out_channel = ref stdout

let open_out_file f =
  let f = if !output_dir <> "" && Filename.is_relative f then Filename.concat !output_dir f else f in
    out_channel := open_out f

let close_out_file () = close_out !out_channel


let header_trailer = ref true
let quiet = ref true
let light = ref false
let gallina = ref false
let short = ref false
let index = ref true
let multi_index = ref false
let toc = ref false
let page_title = ref ""
let title = ref ""
let externals = ref true
let coqlib = ref "http://coq.inria.fr/library/"
let coqlib_path = ref Coq_config.coqlib
let raw_comments = ref false

let charset = ref "iso-8859-1"
let inputenc = ref ""
let latin1 = ref false
let utf8 = ref false

let set_latin1 () =
  charset := "iso-8859-1";
  inputenc := "latin1";
  latin1 := true

let set_utf8 () =
  charset := "utf-8";
  inputenc := "utf8";
  utf8 := true

(* Parsing options *)

type coq_module = string

type file =
  | Vernac_file of string * coq_module
  | Latex_file of string
      
