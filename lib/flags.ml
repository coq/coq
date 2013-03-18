(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

let with_option o f x =
  let old = !o in o:=true;
  try let r = f x in o := old; r
  with reraise -> o := old; raise reraise

let without_option o f x =
  let old = !o in o:=false;
  try let r = f x in o := old; r
  with reraise -> o := old; raise reraise

let boot = ref false

let batch_mode = ref false

let debug = ref false

let print_emacs = ref false

let term_quality = ref false

let xml_export = ref false

type load_proofs = Force | Lazy | Dont

let load_proofs = ref Lazy

let raw_print = ref false

let record_print = ref true

(* Compatibility mode *)

(* Current means no particular compatibility consideration.
   For correct comparisons, this constructor should remain the last one. *)

type compat_version = V8_2 | V8_3 | Current
let compat_version = ref Current
let version_strictly_greater v = !compat_version > v
let version_less_or_equal v = not (version_strictly_greater v)

let pr_version = function
  | V8_2 -> "8.2"
  | V8_3 -> "8.3"
  | Current -> "current"

(* Translate *)
let beautify = ref false
let make_beautify f = beautify := f
let do_beautify () = !beautify
let beautify_file = ref false

(* Silent / Verbose *)
let silent = ref false
let make_silent flag = silent := flag; ()
let is_silent () = !silent
let is_verbose () = not !silent

let silently f x = with_option silent f x
let verbosely f x = without_option silent f x

let if_silent f x = if !silent then f x
let if_verbose f x = if not !silent then f x

let auto_intros = ref true
let make_auto_intros flag = auto_intros := flag
let is_auto_intros () = version_strictly_greater V8_2 && !auto_intros

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

module Stringset = Set.Make(struct type t = string let compare = compare end)

let unsafe_set = ref Stringset.empty
let add_unsafe s = unsafe_set := Stringset.add s !unsafe_set
let is_unsafe s = Stringset.mem s !unsafe_set

(* Flags for external tools *)

let subst_command_placeholder s t =
  let buff = Buffer.create (String.length s + String.length t) in
  let i = ref 0 in
  while (!i < String.length s) do
    if s.[!i] = '%' & !i+1 < String.length s & s.[!i+1] = 's'
    then (Buffer.add_string buff t;incr i)
    else Buffer.add_char buff s.[!i];
    incr i
  done;
  Buffer.contents buff

let browser_cmd_fmt =
 try
  let coq_netscape_remote_var = "COQREMOTEBROWSER" in
  Sys.getenv coq_netscape_remote_var
 with
  Not_found -> Coq_config.browser

let is_standard_doc_url url =
  let wwwcompatprefix = "http://www.lix.polytechnique.fr/coq/" in
  let n = String.length Coq_config.wwwcoq in
  let n' = String.length Coq_config.wwwrefman in
  url = Coq_config.localwwwrefman ||
  url = Coq_config.wwwrefman ||
  url = wwwcompatprefix ^ String.sub Coq_config.wwwrefman n (n'-n)

(* same as in System, but copied here because of dependencies *)
let canonical_path_name p =
  let current = Sys.getcwd () in
  Sys.chdir p;
  let result = Sys.getcwd () in
  Sys.chdir current;
  result

(* Options for changing coqlib *)
let coqlib_spec = ref false
let coqlib = ref (
  (* same as Envars.coqroot, but copied here because of dependencies *)
  Filename.dirname
    (canonical_path_name (Filename.dirname Sys.executable_name))
)

(* Options for changing camlbin (used by coqmktop) *)
let camlbin_spec = ref false
let camlbin = ref Coq_config.camlbin

(* Options for changing camlp4bin (used by coqmktop) *)
let camlp4bin_spec = ref false
let camlp4bin = ref Coq_config.camlp4bin

(* Level of inlining during a functor application *)

let default_inline_level = 100
let inline_level = ref default_inline_level
let set_inline_level = (:=) inline_level
let get_inline_level () = !inline_level
