(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
open Util
open Nativevalues
open Nativecode
open Errors
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

(* Global settings and utilies for interface with OCaml *)
let compiler_name =
  Filename.quote (if Dynlink.is_native then ocamlopt () else ocamlc ())

let ( / ) = Filename.concat

(* We have to delay evaluation of include_dirs because coqlib cannot be guessed
until flags have been properly initialized *)
let include_dirs () =
  [Filename.temp_dir_name; coqlib () / "kernel"; coqlib () / "library"]

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

let call_compiler ml_filename load_path =
  let load_path = List.map (fun dn -> dn / output_dir) load_path in
  let include_dirs = List.map Filename.quote (include_dirs () @ load_path) in
  let include_dirs = String.concat " -I " include_dirs in
  let f = Filename.chop_extension ml_filename in
  let link_filename = f ^ ".cmo" in
  let link_filename = Dynlink.adapt_filename link_filename in
  let comp_cmd =
    Format.sprintf "%s -%s -o %s -rectypes -w a -I %s -impl %s"
      compiler_name (if Dynlink.is_native then "shared" else "c")
      (Filename.quote link_filename) include_dirs (Filename.quote ml_filename)
  in
  Sys.command comp_cmd, link_filename

let compile fn code =
  write_ml_code fn code;
  call_compiler fn (!get_load_paths())

let compile_library dir code load_path fn =
  let header = mk_library_header dir in
  let fn = fn ^ source_ext in
  let basename = Filename.basename fn in
  let dirname = Filename.dirname fn in
  let dirname = dirname / output_dir in
  if not (Sys.file_exists dirname) then Unix.mkdir dirname 0o755;
  let fn = dirname / basename in
  write_ml_code fn ~header code;
  fst (call_compiler fn load_path)

(* call_linker links dynamically the code for constants in environment or a  *)
(* conversion test. Silently fails if the file does not exist in bytecode    *)
(* mode, since the standard library is not compiled to bytecode with default *)
(* settings.                                                                 *)
let call_linker ?(fatal=true) prefix f upds =
  rt1 := dummy_value ();
  rt2 := dummy_value ();
  if Dynlink.is_native || Sys.file_exists f then
  (try
    if Dynlink.is_native then Dynlink.loadfile f else !load_obj f;
    register_native_file prefix
   with | Dynlink.Error e ->
          let msg = "Dynlink error, " ^ Dynlink.error_message e in
          if fatal then anomaly (Pp.str msg) else Pp.msg_warning (Pp.str msg)
        | e when Errors.noncritical e ->
          let msg = "Dynlink error" in
          if fatal then anomaly (Pp.str msg) else Pp.msg_warning (Pp.str msg));
  match upds with Some upds -> update_locations upds | _ -> ()

let link_library ~prefix ~dirname ~basename =
  let f = dirname / output_dir / basename in
  call_linker ~fatal:false prefix f None
