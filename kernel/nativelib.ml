(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Util
open Nativevalues
open Nativecode
open CErrors

(** This file provides facilities to access OCaml compiler and dynamic linker,
used by the native compiler. *)

let get_load_paths =
  ref (fun _ -> anomaly (Pp.str "get_load_paths not initialized.") : unit -> string list)

let open_header = ["Nativevalues";
                   "Nativecode";
                   "Nativelib";
                   "Nativeconv"]
let open_header = List.map mk_open open_header

(* Directory where compiled files are stored *)
let dft_output_dir = ".coq-native"
let output_dir = ref dft_output_dir

(* Extension of generated ml files, stored for debugging purposes *)
let source_ext = ".native"

let ( / ) = Filename.concat

(* Directory for temporary files for the conversion and normalisation
   (as opposed to compiling the library itself, which uses [output_dir]). *)
let my_temp_dir = lazy (CUnix.mktemp_dir "Coq_native" "")

let () = at_exit (fun () ->
    if not (keep_debug_files ()) && Lazy.is_val my_temp_dir then
      try
        let d = Lazy.force my_temp_dir in
        Array.iter (fun f -> Sys.remove (Filename.concat d f)) (Sys.readdir d);
        Unix.rmdir d
      with (Unix.Unix_error _ | Sys_error _) as e ->
        Feedback.msg_warning
          Pp.(str "Native compile: failed to cleanup: " ++
              str(Printexc.to_string e) ++ fnl()))

let delay_cleanup_file =
  let toclean = ref [] in
  let () = at_exit (fun () -> List.iter (fun f -> if Sys.file_exists f then Sys.remove f) !toclean) in
  fun f -> if not (keep_debug_files()) then toclean := f :: !toclean

(* We have to delay evaluation of include_dirs because coqlib cannot
   be guessed until flags have been properly initialized. It also lets
   us avoid forcing [my_temp_dir] if we don't need it (eg stdlib file
   without native compute or native conv uses). *)
let include_dirs = ref []

let get_include_dirs () =
  let base = match !include_dirs with
  | [] ->
    (* EJGA: Should this case go away in favor of always requiring
       explicit -nI flags once we remove the make-based system? I think
       so. *)
    let env = Boot.Env.init () in
    [ Boot.Env.(Path.to_string (native_cmi env "kernel"))
    ; Boot.Env.(Path.to_string (native_cmi env "library"))
    ]
  | _::_ as l -> l
  in
  if Lazy.is_val my_temp_dir
  then (Lazy.force my_temp_dir) :: base
  else base

(* Pointer to the function linking an ML object into Rocq's toplevel *)
let load_obj = ref (fun _x -> () : string -> unit)

let rt1 = ref (dummy_value ())
let rt2 = ref (dummy_value ())

let get_ml_filename () =
  let temp_dir = Lazy.force my_temp_dir in
  let filename = Filename.temp_file ~temp_dir "Coq_native" source_ext in
  let prefix = Filename.chop_extension (Filename.basename filename) ^ "." in
  filename, prefix

let write_ml_code fn ?(header=[]) code =
  let header = open_header@header in
  let ch_out = open_out fn in
  let fmt = Format.formatter_of_out_channel ch_out in
  List.iter (pp_global fmt) (header@code);
  close_out ch_out

let error_native_compiler_failed e =
  let msg = match e with
  | Inl (Unix.WEXITED 127) -> Pp.(strbrk "The OCaml compiler was not found. Make sure it is installed, together with findlib.")
  | Inl (Unix.WEXITED n) ->
     Pp.(strbrk "Native compiler exited with status" ++ str" " ++ int n
         ++ strbrk (if n = 2 then " (in case of stack overflow, increasing stack size (typically with \"ulimit -s\") often helps)" else ""))
  | Inl (Unix.WSIGNALED n) -> Pp.(strbrk "Native compiler killed by signal" ++ str" " ++ int n)
  | Inl (Unix.WSTOPPED n) -> Pp.(strbrk "Native compiler stopped by signal" ++ str" " ++ int n)
  | Inr e -> Pp.(strbrk "Native compiler failed with error: " ++ strbrk (Unix.error_message e))
  in
  CErrors.user_err msg

let call_compiler ?profile:(profile=false) ml_filename =
  (* The below path is computed from Require statements, by uniquizing
     the paths, see [Library.get_used_load_paths] This is in general
     hacky and we should do a bit better once we move loadpath to its
     own library *)
  let require_load_path = !get_load_paths () in
  (* We assume that installed files always go in .coq-native for now *)
  (* To ease the build we also consider the current dir, but at some point the build system should manage both *)
  let install_load_path = List.map (fun dn -> dn / dft_output_dir) require_load_path @ require_load_path in
  let include_dirs = List.flatten (List.map (fun x -> ["-I"; x]) (get_include_dirs () @ install_load_path)) in
  let f = Filename.chop_extension ml_filename in
  let link_filename = f ^ ".cmo" in
  let link_filename = Dynlink.adapt_filename link_filename in
  let remove f = if Sys.file_exists f then Sys.remove f in
  remove link_filename;
  remove (f ^ ".cmi");
  let initial_args =
    if Dynlink.is_native then
      ["opt"; "-shared"]
     else
      ["ocamlc"; "-c"]
  in
  let profile_args =
    if profile then
      ["-g"]
    else
      []
  in
  let flambda_args = if Sys.(backend_type = Native) then ["-Oclassic"] else [] in
  let args =
    initial_args @
      profile_args @
        flambda_args @
      ("-o"::link_filename
       ::"-rectypes"
       ::"-w"::"a"
       ::include_dirs) @
    ["-impl"; ml_filename] in
  let ocamlfind = Boot.Env.ocamlfind () in
  debug_native_compiler (fun () -> Pp.str (ocamlfind ^ " " ^ (String.concat " " args)));
  try
    let res = CUnix.sys_command ocamlfind args in
    match res with
    | Unix.WEXITED 0 -> link_filename
    | Unix.WEXITED _n | Unix.WSIGNALED _n | Unix.WSTOPPED _n ->
      error_native_compiler_failed (Inl res)
  with Unix.Unix_error (e,_,_) ->
    error_native_compiler_failed (Inr e)

let compile fn code ~profile:profile =
  write_ml_code fn code;
  let r = call_compiler ~profile fn in
  (* NB: to prevent reusing the same filename we MUST NOT remove the file until exit
     cf #15263 *)
  delay_cleanup_file fn;
  r

type native_library = Nativecode.global list * Nativevalues.symbols

let compile_library (code, symb) fn =
  let header = mk_library_header symb in
  let fn = fn ^ source_ext in
  let basename = Filename.basename fn in
  let dirname =
    if Filename.is_relative !output_dir then Filename.dirname fn / !output_dir else !output_dir in
  let () =
    try Unix.mkdir dirname 0o755
    with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  in
  let fn = dirname / basename in
  write_ml_code fn ~header code;
  let _ = call_compiler fn in
  delay_cleanup_file fn

let execute_library ~prefix f upds =
  rt1 := dummy_value ();
  rt2 := dummy_value ();
  if not (Sys.file_exists f) then
    CErrors.user_err Pp.(str "Cannot find native compiler file " ++ str f);
  if Dynlink.is_native then Dynlink.loadfile f else !load_obj f;
  register_native_file prefix;
  update_locations upds;
  (!rt1, !rt2)

let link_library dirname prefix =
  let basename = Dynlink.adapt_filename (prefix ^ "cmo") in
  (* We try both [output_dir] and [.coq-native], unfortunately from
     [Require] we don't know if we are loading a library in the build
     dir or in the installed layout *)
  let install_location = dirname / dft_output_dir / basename in
  let build_location = dirname / !output_dir / basename in
  let f = if Sys.file_exists build_location then build_location else install_location in
  try
    if Dynlink.is_native then Dynlink.loadfile f else !load_obj f;
    register_native_file prefix
  with
  | Dynlink.Error _ as exn ->
      debug_native_compiler (fun () -> CErrors.iprint (Exninfo.capture exn))

let delayed_link = ref []

let link_libraries () =
  let delayed = List.rev !delayed_link in
  delayed_link := [];
  List.iter (fun (dirname, libname) ->
      let prefix = mod_uid_of_dirpath libname ^ "." in
      if not (Nativecode.is_loaded_native_file prefix) then
        link_library dirname prefix
    ) delayed

let enable_library dirname libname =
  delayed_link := (dirname, libname) :: !delayed_link
