(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
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

let record_aux_file = ref false

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

type compat_version = V8_8 | V8_9 | Current

let compat_version = ref Current

let version_compare v1 v2 = match v1, v2 with
  | V8_8, V8_8 -> 0
  | V8_8, _ -> -1
  | _, V8_8 -> 1
  | V8_9, V8_9 -> 0
  | V8_9, _ -> -1
  | _, V8_9 -> 1
  | Current, Current -> 0

let version_strictly_greater v = version_compare !compat_version v > 0
let version_less_or_equal v = not (version_strictly_greater v)

let pr_version = function
  | V8_8 -> "8.8"
  | V8_9 -> "8.9"
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

let warn = ref true
let make_warn flag = warn := flag;  ()
let if_warn f x = if !warn then f x

(* Level of inlining during a functor application *)

let default_inline_level = 100
let inline_level = ref default_inline_level
let set_inline_level = (:=) inline_level
let get_inline_level () = !inline_level

let profile_ltac = ref false
let profile_ltac_cutoff = ref 2.0
