
(* $Id$ *)

open Pp
open Util
open System
open Options
open States
open Toplevel
open Coqinit

let print_header () =
  Printf.printf "Welcome to Coq %s (%s)\n" Coq_config.version Coq_config.date;
  flush stdout

let set_batch_mode () = batch_mode := true

let remove_top_ml () = Mltop.remove ()

let inputstate = ref "initial.coq"
let set_inputstate s = inputstate:= s
let inputstate () =
  if !inputstate <> "" then begin
    intern_state !inputstate;
    Lib.declare_initial_state()
  end

let outputstate = ref ""
let set_outputstate s = outputstate:=s
let outputstate () = if !outputstate <> "" then extern_state !outputstate

let load_vernacular_list = ref ([] : string list)
let add_load_vernacular s =
  load_vernacular_list := (make_suffix s ".v") :: !load_vernacular_list
let load_vernacular () =
  List.iter
    (fun s -> Vernac.load_vernac false s)
    (List.rev !load_vernacular_list)

let load_vernacular_obj = ref ([] : string list)
let add_vernac_obj s = load_vernacular_obj := s :: !load_vernacular_obj
let load_vernac_obj () = 
  List.iter
    (fun s -> Library.load_module (Filename.basename s) (Some s))
    (List.rev !load_vernacular_obj)

let require_list = ref ([] : string list)
let add_require s = require_list := s :: !require_list
let require () =
  List.iter
    (fun s -> Library.require_module None (Filename.basename s) (Some s) false)
    (List.rev !require_list)

(* Re-exec Coq in bytecode or native code if necessary. [s] is either
   ["byte"] or ["opt"]. Notice that this is possible since the nature of
   the toplevel has already been set in [Mltop] by the main file created
   by coqmktop (see scripts/coqmktop.ml). *)

let re_exec s =
  let is_native = (Mltop.get()) = Mltop.Native in
  if (is_native && s = "byte") || ((not is_native) && s = "opt") then 
    let prog = Sys.argv.(0) in
    let newprog = Filename.concat (Filename.dirname prog) ("coqtop." ^ s) in
    Sys.argv.(0) <- newprog;
    Unix.execv newprog Sys.argv

(* Parsing of the command line.
 *
 * We no longer use Arg.parse, in order to use share Usage.print_usage 
 * between coqtop and coqc. *)

let usage () =
  if !batch_mode then
    Usage.print_usage_coqc ()
  else
    Usage.print_usage_coqtop () ;
  flush stderr ;
  exit 1

let parse_include d =
  try
    let pos = String.index d '=' in
    (String.sub d 0 pos,
     Names.dirpath_of_string (String.sub d (pos+1) (String.length d - pos -1)))
  with Not_found ->
    let alias = Filename.basename d in
    let alias =
      if alias = "." then
	Filename.basename (Unix.getcwd ())
      else if alias = ".." then
	Filename.basename (Filename.dirname (Unix.getcwd ()))
      else alias in
    if not (Names.is_ident alias) then 
      error ("Cannot find a name to which "^d^" may map in Coq library");
    (d, [alias])

let warning s = wARNING [< 'sTR s >]

let parse_args () =
  let rec parse = function
    | [] -> ()

    | ("-I"|"-include") :: d :: rem -> push_include (parse_include d);parse rem
    | ("-I"|"-include") :: []       -> usage ()

    | "-R" :: d :: rem -> push_rec_include (parse_include d); parse rem
    | "-R" :: []       -> usage ()

    | "-q" :: rem -> no_load_rc (); parse rem

    | "-opt" :: rem -> re_exec "opt"; parse rem
    | "-byte" :: rem -> re_exec "byte"; parse rem
    | "-full" :: rem -> warning "option -full deprecated\n"; parse rem

    | "-batch" :: rem -> set_batch_mode (); parse rem
	     
    | "-outputstate" :: s :: rem -> set_outputstate s; parse rem
    | "-outputstate" :: []       -> usage ()

    | "-nois" :: rem -> set_inputstate ""; parse rem
	     
    | ("-inputstate"|"-is") :: s :: rem -> set_inputstate s; parse rem
    | ("-inputstate"|"-is") :: []       -> usage ()

    | "-load-ml-object" :: f :: rem -> Mltop.dir_ml_load f; parse rem
    | "-load-ml-object" :: []       -> usage ()

    | "-load-ml-source" :: f :: rem -> Mltop.dir_ml_use f; parse rem
    | "-load-ml-source" :: []       -> usage ()

    | "-load-vernac-source" :: f :: rem -> add_load_vernacular f; parse rem
    | "-load-vernac-source" :: []       -> usage ()

    | "-load-vernac-object" :: f :: rem -> add_vernac_obj f; parse rem
    | "-load-vernac-object" :: []       -> usage ()

    | "-require" :: f :: rem -> add_require f; parse rem
    | "-require" :: []       -> usage ()

    | "-unsafe" :: f :: rem -> add_unsafe f; parse rem
    | "-unsafe" :: []       -> usage ()

    | "-debug" :: rem -> set_debug (); parse rem

    | "-emacs" :: rem -> Options.print_emacs := true; parse rem
	  
    | "-where" :: _ -> print_endline Coq_config.coqlib; exit 0

    | ("-quiet"|"-silent") :: rem -> Options.make_silent true; parse rem

    | ("-?"|"-h"|"-H"|"-help"|"--help") :: _ -> usage ()

    | ("-v"|"--version") :: _ -> Usage.version ()

    | "-init-file" :: f :: rem -> set_rcfile f; parse rem
    | "-init-file" :: []       -> usage ()

    | "-user" :: u :: rem -> set_rcuser u; parse rem
    | "-user" :: []       -> usage ()

    | "-notactics" :: rem -> remove_top_ml (); parse rem

    | "-just-parsing" :: rem -> Vernac.just_parsing := true; parse rem

    | s :: _ -> prerr_endline ("Don't know what to do with " ^ s); usage ()

  in
  try
    parse (List.tl (Array.to_list Sys.argv))
  with 
    | UserError(_,s) as e -> begin
	try
	  Stream.empty s; exit 1
	with Stream.Failure ->
	  mSGNL (Errors.explain_exn e); exit 1
      end
    | e -> begin mSGNL (Errors.explain_exn e); exit 1 end


(* To prevent from doing the initialization twice *)
let initialized = ref false

(* Ctrl-C is fatal during the initialisation *)
let start () =
  if not !initialized then begin
    initialized := true;
    Sys.catch_break false;
    Lib.init();
    try
      parse_args ();
      if is_verbose() then print_header ();
      init_load_path ();
      inputstate ();
      load_vernac_obj ();
      require ();
      load_rcfile();
      load_vernacular ();
      outputstate ()
    with e ->
      flush_all();
      if not !batch_mode then message "Error during initialization :";
      mSGNL (Toplevel.print_toplevel_error e);
      exit 1
  end;
  if !batch_mode then (flush_all(); Profile.print_profile ();exit 0);
  Toplevel.loop()

(* Coqtop.start will be called by the code produced by coqmktop *)
