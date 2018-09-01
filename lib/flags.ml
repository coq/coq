(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* If [restore] is false, whenever [f] modifies the ref, we will
   preserve the modification. *)
let with_modified_ref ?(restore=true) r nf f x =
  let old_ref = !r in r := nf !r;
  try
    let pre = !r in
    let res = f x in
    (* If r was modified don't restore its old value *)
    if restore || pre == !r then r := old_ref;
    res
  with reraise ->
    let reraise = Backtrace.add_backtrace reraise in
    r := old_ref;
    Exninfo.iraise reraise

let with_option o f x = with_modified_ref ~restore:false o (fun _ -> true) f x
let without_option o f x = with_modified_ref ~restore:false o (fun _ -> false) f x
let with_extra_values o l f x = with_modified_ref o (fun ol -> ol@l) f x

(* hide the [restore] option as internal *)
let with_modified_ref r nf f x = with_modified_ref r nf f x

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

let boot = ref false

let record_aux_file = ref false

let test_mode = ref false

let async_proofs_worker_id = ref "master"
let async_proofs_is_worker () = !async_proofs_worker_id <> "master"

let debug = ref false

let in_debugger = ref false
let in_toplevel = ref false

let profile = false

let raw_print = ref false

let we_are_parsing = ref false

(* Compatibility mode *)

(* Current means no particular compatibility consideration.
   For correct comparisons, this constructor should remain the last one. *)

type compat_version = V8_7 | V8_8 | Current

let compat_version = ref Current

let version_compare v1 v2 = match v1, v2 with
  | V8_7, V8_7 -> 0
  | V8_7, _ -> -1
  | _, V8_7 -> 1
  | V8_8, V8_8 -> 0
  | V8_8, _ -> -1
  | _, V8_8 -> 1
  | Current, Current -> 0

let version_strictly_greater v = version_compare !compat_version v > 0
let version_less_or_equal v = not (version_strictly_greater v)

let pr_version = function
  | V8_7 -> "8.7"
  | V8_8 -> "8.8"
  | Current -> "current"

(* Translate *)
let beautify = ref false
let beautify_file = ref false

(* Silent / Verbose *)
let quiet = ref false
let silently f x = with_option quiet f x
let verbosely f x = without_option quiet f x

let if_silent f x = if !quiet then f x
let if_verbose f x = if not !quiet then f x

let auto_intros = ref true
let make_auto_intros flag = auto_intros := flag
let is_auto_intros () = !auto_intros

let universe_polymorphism = ref false
let make_universe_polymorphism b = universe_polymorphism := b
let is_universe_polymorphism () = !universe_polymorphism

let polymorphic_inductive_cumulativity = ref false
let make_polymorphic_inductive_cumulativity b = polymorphic_inductive_cumulativity := b
let is_polymorphic_inductive_cumulativity () = !polymorphic_inductive_cumulativity

(** [program_mode] tells that Program mode has been activated, either
    globally via [Set Program] or locally via the Program command prefix. *)

let program_mode = ref false
let is_program_mode () = !program_mode

let warn = ref true
let make_warn flag = warn := flag;  ()
let if_warn f x = if !warn then f x

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

(* Level of inlining during a functor application *)

let default_inline_level = 100
let inline_level = ref default_inline_level
let set_inline_level = (:=) inline_level
let get_inline_level () = !inline_level

(* Native code compilation for conversion and normalization *)
let output_native_objects = ref false

(* Print the mod uid associated to a vo file by the native compiler *)
let print_mod_uid = ref false

let profile_ltac = ref false
let profile_ltac_cutoff = ref 2.0
