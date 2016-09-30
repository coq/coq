(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
open Util
open Nativevalues
open Nativecode
open CErrors
open Envars

(** This file provides facilities to access OCaml compiler and dynamic linker,
used by the native compiler. *)

let get_load_paths =
  ref (fun _ -> anomaly (Pp.str "get_load_paths not initialized") : unit -> string list)

let open_header = ["Nativevalues";
                   "Nativecode";
                   "Nativelib";
		   "Nativeconv";
                   "Declaremods"]
let open_header = List.map mk_open open_header

(* Directory where compiled files are stored *)
let output_dir = ".coq-native"

(* Extension of genereted ml files, stored for debugging purposes *)
let source_ext = ".native"

let ( / ) = Filename.concat

(* We have to delay evaluation of include_dirs because coqlib cannot be guessed
until flags have been properly initialized *)
let include_dirs () =
  [Filename.get_temp_dir_name (); coqlib () / "kernel"; coqlib () / "library"]

(* Pointer to the function linking an ML object into coq's toplevel *)
let load_obj = ref (fun x -> () : string -> unit)

let rt1 = ref (dummy_value ())
let rt2 = ref (dummy_value ())

let get_ml_filename () =
  let filename = Filename.temp_file "Coq_native" source_ext in
  let prefix = Filename.chop_extension (Filename.basename filename) ^ "." in
  filename, prefix

let write_ml_code fn ?(header=[]) code =
  let header = open_header@header in
  let ch_out = open_out fn in
  let fmt = Format.formatter_of_out_channel ch_out in
  List.iter (pp_global fmt) (header@code);
  close_out ch_out

let warn_native_compiler_failed =
  let print = function
  | Inl (Unix.WEXITED n) -> Pp.(strbrk "Native compiler exited with status" ++ str" " ++ int n)
  | Inl (Unix.WSIGNALED n) -> Pp.(strbrk "Native compiler killed by signal" ++ str" " ++ int n)
  | Inl (Unix.WSTOPPED n) -> Pp.(strbrk "Native compiler stopped by signal" ++ str" " ++ int n)
  | Inr e -> Pp.(strbrk "Native compiler failed with error: " ++ strbrk (Unix.error_message e))
  in
  CWarnings.create ~name:"native-compiler-failed" ~category:"native-compiler" print

let call_compiler ml_filename =
  let load_path = !get_load_paths () in
  let load_path = List.map (fun dn -> dn / output_dir) load_path in
  let include_dirs = List.flatten (List.map (fun x -> ["-I"; x]) (include_dirs () @ load_path)) in
  let f = Filename.chop_extension ml_filename in
  let link_filename = f ^ ".cmo" in
  let link_filename = Dynlink.adapt_filename link_filename in
  let remove f = if Sys.file_exists f then Sys.remove f in
  remove link_filename;
  remove (f ^ ".cmi");
  let args =
    (if Dynlink.is_native then "opt" else "ocamlc")
    ::(if Dynlink.is_native then "-shared" else "-c")
    ::"-o"::link_filename
    ::"-rectypes"
    ::"-w"::"a"
    ::include_dirs
    @ ["-impl"; ml_filename] in
  if !Flags.debug then Feedback.msg_debug (Pp.str (ocamlfind () ^ " " ^ (String.concat " " args)));
  try
    let res = CUnix.sys_command (ocamlfind ()) args in
    let res = match res with
      | Unix.WEXITED 0 -> true
      | Unix.WEXITED n | Unix.WSIGNALED n | Unix.WSTOPPED n ->
        warn_native_compiler_failed (Inl res); false
    in
    res, link_filename
  with Unix.Unix_error (e,_,_) ->
    warn_native_compiler_failed (Inr e);
    false, link_filename

let compile fn code =
  write_ml_code fn code;
  let r = call_compiler fn in
  if (not !Flags.debug) && Sys.file_exists fn then Sys.remove fn;
  r

let compile_library dir code fn =
  let header = mk_library_header dir in
  let fn = fn ^ source_ext in
  let basename = Filename.basename fn in
  let dirname = Filename.dirname fn in
  let dirname = dirname / output_dir in
  let () =
    try Unix.mkdir dirname 0o755
    with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  in
  let fn = dirname / basename in
  write_ml_code fn ~header code;
  let r = fst (call_compiler fn) in
  if (not !Flags.debug) && Sys.file_exists fn then Sys.remove fn;
  r

(* call_linker links dynamically the code for constants in environment or a  *)
(* conversion test. *)
let call_linker ?(fatal=true) prefix f upds =
  rt1 := dummy_value ();
  rt2 := dummy_value ();
  if not (Sys.file_exists f) then
    begin
      let msg = "Cannot find native compiler file " ^ f in
      if fatal then CErrors.error msg
      else if !Flags.debug then Feedback.msg_debug (Pp.str msg)
    end
  else
  (try
    if Dynlink.is_native then Dynlink.loadfile f else !load_obj f;
    register_native_file prefix
   with Dynlink.Error e as exn ->
     let exn = CErrors.push exn in
     let msg = "Dynlink error, " ^ Dynlink.error_message e in
     if fatal then (Feedback.msg_error (Pp.str msg); iraise exn)
     else if !Flags.debug then Feedback.msg_debug (Pp.str msg));
  match upds with Some upds -> update_locations upds | _ -> ()

let link_library ~prefix ~dirname ~basename =
  let f = dirname / output_dir / basename in
  call_linker ~fatal:false prefix f None
