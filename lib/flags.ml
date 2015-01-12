(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

let with_option o f x =
  let old = !o in o:=true;
   try let r = f x in if !o = true then o := old; r
   with reraise ->
     let reraise = Backtrace.add_backtrace reraise in
     let () = o := old in
     Exninfo.iraise reraise

let with_options ol f x =
  let vl = List.map (!) ol in
  let () = List.iter (fun r -> r := true) ol in
  try
    let r = f x in
    let () = List.iter2 (:=) ol vl in r
  with reraise ->
    let reraise = Backtrace.add_backtrace reraise in
    let () = List.iter2 (:=) ol vl in
    Exninfo.iraise reraise

let without_option o f x =
  let old = !o in o:=false;
  try let r = f x in if !o = false then o := old; r
  with reraise ->
    let reraise = Backtrace.add_backtrace reraise in
    let () = o := old in
    Exninfo.iraise reraise

let with_extra_values o l f x =
  let old = !o in o:=old@l;
  try let r = f x in o := old; r
  with reraise ->
    let reraise = Backtrace.add_backtrace reraise in
    let () = o := old in
    Exninfo.iraise reraise

let boot = ref false
let load_init = ref true
let batch_mode = ref false

type compilation_mode = BuildVo | BuildVio | Vio2Vo
let compilation_mode = ref BuildVo

type async_proofs = APoff | APonLazy | APon
let async_proofs_mode = ref APoff
type cache = Force
let async_proofs_cache = ref None
let async_proofs_n_workers = ref 1
let async_proofs_n_tacworkers = ref 2
let async_proofs_private_flags = ref None
let async_proofs_full = ref false
let async_proofs_never_reopen_branch = ref false
let async_proofs_flags_for_workers = ref []
let async_proofs_worker_id = ref "master"
type priority = Low | High
let async_proofs_worker_priority = ref Low
let string_of_priority = function Low -> "low" | High -> "high"
let priority_of_string = function
  | "low" -> Low
  | "high" -> High
  | _ -> raise (Invalid_argument "priority_of_string")

let async_proofs_is_worker () =
  !async_proofs_worker_id <> "master"
let async_proofs_is_master () =
  !async_proofs_mode = APon && !async_proofs_worker_id = "master"

let debug = ref false
let in_debugger = ref false
let in_toplevel = ref false

let profile = false

let print_emacs = ref false
let coqtop_ui = ref false

let ide_slave = ref false
let ideslave_coqtop_flags = ref None

let time = ref false

let raw_print = ref false

let record_print = ref true

let univ_print = ref false

let we_are_parsing = ref false

(* Compatibility mode *)

(* Current means no particular compatibility consideration.
   For correct comparisons, this constructor should remain the last one. *)

type compat_version = V8_2 | V8_3 | V8_4 | Current

let compat_version = ref Current

let version_strictly_greater v = match !compat_version, v with
| V8_2, (V8_2 | V8_3 | V8_4 | Current) -> false
| V8_3, (V8_3 | V8_4 | Current) -> false
| V8_4, (V8_4 | Current) -> false
| Current, Current -> false
| V8_3, V8_2 -> true
| V8_4, (V8_2 | V8_3) -> true
| Current, (V8_2 | V8_3 | V8_4) -> true

let version_less_or_equal v = not (version_strictly_greater v)

let pr_version = function
  | V8_2 -> "8.2"
  | V8_3 -> "8.3"
  | V8_4 -> "8.4"
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

let universe_polymorphism = ref false
let make_universe_polymorphism b = universe_polymorphism := b
let is_universe_polymorphism () = !universe_polymorphism

let local_polymorphic_flag = ref None
let use_polymorphic_flag () = 
  match !local_polymorphic_flag with 
  | Some p -> local_polymorphic_flag := None; p
  | None -> is_universe_polymorphism ()
let make_polymorphic_flag b =
  local_polymorphic_flag := Some b

(** [program_mode] tells that Program mode has been activated, either
    globally via [Set Program] or locally via the Program command prefix. *)

let program_mode = ref false
let is_program_mode () = !program_mode

let warn = ref true
let make_warn flag = warn := flag;  ()
let if_warn f x = if !warn then f x

(* The number of printed hypothesis in a goal *)

let print_hyps_limit = ref (None : int option)
let set_print_hyps_limit n = print_hyps_limit := n
let print_hyps_limit () = !print_hyps_limit

(* Flags for external tools *)

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

(* Options for changing coqlib *)
let coqlib_spec = ref false
let coqlib = ref "(not initialized yet)"

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

(* Disabling native code compilation for conversion and normalization *)
let no_native_compiler = ref Coq_config.no_native_compiler

(* Print the mod uid associated to a vo file by the native compiler *)
let print_mod_uid = ref false

let tactic_context_compat = ref false
