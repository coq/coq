(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* If [restore] is false, whenever [f] modifies the ref, we will
   preserve the modification. *)
let with_modified_ref ?(restore=true) r nf f x =
  let acquire x = let old_ref = !r in r := nf !r; (old_ref, !r, x) in
  let release (old_ref, pre, _) =
    (* If r was modified don't restore its old value *)
    if restore || pre == !r then r := old_ref;
    r := old_ref
  in
  let scope (old_ref, pre, x) = f x in
  Memprof_coq.Masking.with_resource ~acquire x ~scope ~release

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
    let reraise = Exninfo.capture reraise in
    let () = List.iter2 (:=) ol vl in
    Exninfo.iraise reraise

let async_proofs_worker_id = ref "master"
let async_proofs_is_worker () = !async_proofs_worker_id <> "master"

let load_vos_libraries = ref false

let xml_debug = ref false

let in_debugger = ref false
let in_ml_toplevel = ref false

let raw_print = ref false

let in_synterp_phase = ref false

(* Translate *)
let beautify = ref false
let beautify_file = ref false
let record_comments = ref false

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

(* Default output directory *)

let output_directory = ref None

let test_mode = ref false
