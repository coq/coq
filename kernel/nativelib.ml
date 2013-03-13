(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
open Names
open Term
open Util
open Nativevalues
open Declarations
open Nativecode
open Pre_env
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

(* Global settings and utilies for interface with OCaml *)
let compiler_name =
  Filename.quote (if Dynlink.is_native then ocamlopt () else ocamlc ())

let ( / ) a b = Filename.concat a b

(* We have to delay evaluation of include_dirs because coqlib cannot be guessed
until flags have been properly initialized *)
let include_dirs () = [Filename.temp_dir_name;
                    coqlib ~fail:Errors.error / "kernel";
                    coqlib ~fail:Errors.error / "library"]

(* Pointer to the function linking an ML object into coq's toplevel *)
let load_obj = ref (fun x -> () : string -> unit)

let rt1 = ref (dummy_value ())
let rt2 = ref (dummy_value ())

let get_ml_filename () =
  let filename = Filename.temp_file "Coq_native" ".ml" in
  let prefix = Filename.chop_extension (Filename.basename filename) ^ "." in
  filename, prefix

let write_ml_code ml_filename ?(header=[]) code =
  let header = open_header@header in
  let ch_out = open_out ml_filename in
  let fmt = Format.formatter_of_out_channel ch_out in
  List.iter (pp_global fmt) (header@code);
  close_out ch_out

let call_compiler ml_filename load_path =
  let include_dirs = List.map Filename.quote (include_dirs () @ load_path) in
  let include_dirs = String.concat " -I " include_dirs in
  let f = Filename.chop_extension ml_filename in
  let link_filename = f ^ ".cmo" in
  let link_filename = Dynlink.adapt_filename link_filename in
  let comp_cmd =
    Format.sprintf "%s -%s -o %s -rectypes -w a -I %s %s"
      compiler_name (if Dynlink.is_native then "shared" else "c")
      (Filename.quote link_filename) include_dirs (Filename.quote ml_filename)
  in
  let res = Sys.command comp_cmd in
  Sys.rename (f^".ml") (f^".native");
  res, link_filename

let compile ml_filename code =
  write_ml_code ml_filename code;
  call_compiler ml_filename (!get_load_paths())

(* call_linker dynamic links code for constants in environment or a          *)
(* conversion test. Silently fails if the file does not exist in bytecode    *)
(* mode, since the standard library is not compiled to bytecode with default *)
(* settings.                                                                 *)
let call_linker ~fatal prefix f upds =
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
