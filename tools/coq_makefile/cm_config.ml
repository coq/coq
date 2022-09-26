let parse_env_line l =
  try Scanf.sscanf l "%[^=]=%S" (fun name value -> Some(name,value))
  with _ -> None

let with_ic file f =
  let ic = open_in file in
  try
    let rc = f ic in
    close_in ic;
    rc
  with e -> close_in ic; raise e

let getenv_from_file name =
  let base = Filename.dirname Sys.executable_name in
  try
    with_ic (base ^ "/coq_environment.txt") (fun ic ->
      let rec find () =
        let l = input_line ic in
        match parse_env_line l with
        | Some(n,v) when n = name -> v
        | _ -> find ()
      in
        find ())
  with
  | Sys_error s -> raise Not_found
  | End_of_file -> raise Not_found

let system_getenv name =
  try Sys.getenv name with Not_found -> getenv_from_file name

let getenv_else s dft = try system_getenv s with Not_found -> dft ()

let coqbin =
  CUnix.canonical_path_name (Filename.dirname Sys.executable_name)

(** The following only makes sense when executables are running from
    source tree (e.g. during build or in local mode). *)
let coqroot =
  Filename.dirname coqbin

(** Add a local installation suffix (unless the suffix is itself
    absolute in which case the prefix does not matter) *)
let use_suffix prefix suffix =
  if String.length suffix > 0 && suffix.[0] = '/' then suffix else Filename.concat prefix suffix

let docdir () =
  (* This assumes implicitly that the suffix is non-trivial *)
  let path = use_suffix coqroot Coq_config.docdirsuffix in
  if Sys.file_exists path then path else Coq_config.docdir

let ocamlfind () = getenv_else "OCAMLFIND" (fun () -> Coq_config.ocamlfind)

(* Print the configuration information *)
let print_config  f =
  let prefix_var_name = "COQMF_" in
  let env = Boot.Env.init () in
  let coqlib = Boot.Env.coqlib env |> Boot.Path.to_string in
  let corelib = Boot.Env.corelib env |> Boot.Path.to_string in
  let open Printf in
  fprintf f "%sCOQLIB=%s/\n" prefix_var_name coqlib;
  fprintf f "%sCOQCORELIB=%s/\n" prefix_var_name corelib;
  fprintf f "%sDOCDIR=%s/\n" prefix_var_name (docdir ());
  fprintf f "%sOCAMLFIND=%s\n" prefix_var_name (ocamlfind ());
  fprintf f "%sCAMLFLAGS=%s\n" prefix_var_name Coq_mf_config.caml_flags;
  fprintf f "%sWARN=%s\n" prefix_var_name "-warn-error +a-3";
  fprintf f "%sHASNATDYNLINK=%s\n" prefix_var_name
    (if Coq_config.has_natdynlink then "true" else "false");
  fprintf f "%sCOQ_SRC_SUBDIRS=%s\n" prefix_var_name (String.concat " " Coq_mf_config.all_src_dirs);
  fprintf f "%sCOQ_NATIVE_COMPILER_DEFAULT=%s\n" prefix_var_name
    (match Coq_config.native_compiler with
     | Coq_config.NativeOn {ondemand=false} -> "yes"
     | Coq_config.NativeOff -> "no"
     | Coq_config.NativeOn {ondemand=true} -> "ondemand")
