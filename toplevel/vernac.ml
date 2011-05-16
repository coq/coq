(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Parsing of vernacular. *)

open Pp
open Lexer
open Util
open Flags
open System
open Vernacexpr
open Vernacinterp
open Ppvernac
open Compat

(* The functions in this module may raise (unexplainable!) exceptions.
   Use the module Coqtoplevel, which catches these exceptions
   (the exceptions are explained only at the toplevel). *)

exception DuringCommandInterp of Util.loc * exn

exception HasNotFailed

(* Specifies which file is read. The intermediate file names are
   discarded here. The Drop exception becomes an error. We forget
   if the error ocurred during interpretation or not *)

let raise_with_file file exc =
  let (cmdloc,re) =
    match exc with
      | DuringCommandInterp(loc,e) -> (loc,e)
      | e -> (dummy_loc,e)
  in
  let (inner,inex) =
    match re with
      | Error_in_file (_, (b,f,loc), e) when loc <> dummy_loc ->
          ((b, f, loc), e)
      | Loc.Exc_located (loc, e) when loc <> dummy_loc ->
          ((false,file, loc), e)
      | Loc.Exc_located (_, e) | e -> ((false,file,cmdloc), e)
  in
  raise (Error_in_file (file, inner, disable_drop inex))

let real_error = function
  | Loc.Exc_located (_, e) -> e
  | Error_in_file (_, _, e) -> e
  | e -> e

(** Timeout handling *)

(** A global default timeout, controled by option "Set Default Timeout n".
    Use "Unset Default Timeout" to deactivate it (or set it to 0). *)

let default_timeout = ref None

let _ =
  Goptions.declare_int_option
    { Goptions.optsync  = true;
      Goptions.optname  = "the default timeout";
      Goptions.optkey   = ["Default";"Timeout"];
      Goptions.optread  = (fun () -> !default_timeout);
      Goptions.optwrite = ((:=) default_timeout) }

(** When interpreting a command, the current timeout is initially
    the default one, but may be modified locally by a Timeout command. *)

let current_timeout = ref None

(** Installing and de-installing a timer.
    Note: according to ocaml documentation, Unix.alarm isn't available
    for native win32. *)

let timeout_handler _ = raise Timeout

let set_timeout n =
  let psh =
    Sys.signal Sys.sigalrm (Sys.Signal_handle timeout_handler) in
  ignore (Unix.alarm n);
  Some psh

let default_set_timeout () =
  match !current_timeout with
    | Some n -> set_timeout n
    | None -> None

let restore_timeout = function
  | None -> ()
  | Some psh ->
    (* stop alarm *)
    ignore(Unix.alarm 0);
    (* restore handler *)
    Sys.set_signal Sys.sigalrm psh

(* Opening and closing a channel. Open it twice when verbose: the first
   channel is used to read the commands, and the second one to print them.
   Note: we could use only one thanks to seek_in, but seeking on and on in
   the file we parse seems a bit risky to me.  B.B.  *)

let open_file_twice_if verbosely fname =
  let paths = Library.get_load_paths () in
  let _,longfname =
    find_file_in_path ~warn:(Flags.is_verbose()) paths fname in
  let in_chan = open_in longfname in
  let verb_ch = if verbosely then Some (open_in longfname) else None in
  let po = Pcoq.Gram.parsable (Stream.of_channel in_chan) in
  (in_chan, longfname, (po, verb_ch))

let close_input in_chan (_,verb) =
  try
    close_in in_chan;
    match verb with
      | Some verb_ch -> close_in verb_ch
      | _ -> ()
  with _ -> ()

let verbose_phrase verbch loc =
  let loc = unloc loc in
  match verbch with
    | Some ch ->
	let len = snd loc - fst loc in
	let s = String.create len in
        seek_in ch (fst loc);
        really_input ch s 0 len;
        message s;
        pp_flush()
    | _ -> ()

exception End_of_input

let parse_sentence (po, verbch) =
  match Pcoq.Gram.entry_parse Pcoq.main_entry po with
    | Some (loc,_ as com) -> verbose_phrase verbch loc; com
    | None -> raise End_of_input

(* vernac parses the given stream, executes interpfun on the syntax tree it
 * parses, and is verbose on "primitives" commands if verbosely is true *)

let just_parsing = ref false
let chan_beautify = ref stdout
let beautify_suffix = ".beautified"

let set_formatter_translator() =
  let ch = !chan_beautify in
  let out s b e = output ch s b e in
  Format.set_formatter_output_functions out (fun () -> flush ch);
  Format.set_max_boxes max_int

let pr_new_syntax loc ocom =
  let loc = unloc loc in
  if !beautify_file then set_formatter_translator();
  let fs = States.freeze () in
  let com = match ocom with
    | Some VernacNop -> mt()
    | Some com -> pr_vernac com
    | None -> mt() in
  if !beautify_file then
    msg (hov 0 (comment (fst loc) ++ com ++ comment (snd loc)))
  else
    msgnl (hov 4 (str"New Syntax:" ++ fnl() ++ (hov 0 com)));
  States.unfreeze fs;
  Format.set_formatter_out_channel stdout

let rec vernac_com interpfun (loc,com) =
  let rec interp = function
    | VernacLoad (verbosely, fname) ->
	let fname = expand_path_macros fname in
        (* translator state *)
        let ch = !chan_beautify in
        let cs = Lexer.com_state() in
        let cl = !Pp.comments in
        (* end translator state *)
        (* coqdoc state *)
        let cds = Dumpglob.coqdoc_freeze() in
          if !Flags.beautify_file then
	    begin
              let _,f = find_file_in_path ~warn:(Flags.is_verbose())
		(Library.get_load_paths ())
		(make_suffix fname ".v") in
		chan_beautify := open_out (f^beautify_suffix);
		Pp.comments := []
            end;
          begin
	    try
	      read_vernac_file verbosely (make_suffix fname ".v");
              if !Flags.beautify_file then close_out !chan_beautify;
              chan_beautify := ch;
              Lexer.restore_com_state cs;
              Pp.comments := cl;
              Dumpglob.coqdoc_unfreeze cds
	    with e ->
	      if !Flags.beautify_file then close_out !chan_beautify;
              chan_beautify := ch;
              Lexer.restore_com_state cs;
              Pp.comments := cl;
              Dumpglob.coqdoc_unfreeze cds;
	      raise e
	  end

    | VernacList l -> List.iter (fun (_,v) -> interp v) l

    | VernacFail v ->
	if not !just_parsing then begin try
	  interp v; raise HasNotFailed
	with e -> match real_error e with
	  | HasNotFailed ->
	      errorlabstrm "Fail" (str "The command has not failed !")
	  | e when Cerrors.is_user_error e ->
	      if_verbose msgnl
		(str "The command has indeed failed with message:" ++
		 fnl () ++ str "=> " ++ hov 0 (Errors.print e))
	  | _ -> raise e (* Anomalies are not catched by Fail *)
	end

    | VernacTime v ->
	if not !just_parsing then begin
	  let tstart = System.get_time() in
          interp v;
	  let tend = System.get_time() in
          msgnl (str"Finished transaction in " ++
                   System.fmt_time_difference tstart tend)
	end

    | VernacTimeout(n,v) ->
	if not !just_parsing then begin
	  current_timeout := Some n;
	  interp v
	end

    | v ->
        if not !just_parsing then
	  let psh = default_set_timeout () in
	  try
            States.with_heavy_rollback interpfun
              Cerrors.process_vernac_interp_error v;
	    restore_timeout psh
	  with e -> restore_timeout psh; raise e
  in
    try
      current_timeout := !default_timeout;
      if do_beautify () then pr_new_syntax loc (Some com);
      interp com
    with e ->
      Format.set_formatter_out_channel stdout;
      raise (DuringCommandInterp (loc, e))

and read_vernac_file verbosely s =
  Flags.make_warn verbosely;
  let interpfun =
    if verbosely then Vernacentries.interp
    else Flags.silently Vernacentries.interp
  in
  let (in_chan, fname, input) =
    open_file_twice_if verbosely s in
  try
    (* we go out of the following infinite loop when a End_of_input is
     * raised, which means that we raised the end of the file being loaded *)
    while true do
      vernac_com interpfun (parse_sentence input);
      pp_flush ()
    done
  with e ->   (* whatever the exception *)
    Format.set_formatter_out_channel stdout;
    close_input in_chan input;    (* we must close the file first *)
    match real_error e with
      | End_of_input ->
          if do_beautify () then pr_new_syntax (make_loc (max_int,max_int)) None
      | _ -> raise_with_file fname e


(* eval_expr : Util.loc * Vernacexpr.vernac_expr -> unit
 * execute one vernacular command. Marks the end of the command in the lib_stk
 * with a new label to make vernac undoing easier. Also freeze state to speed up
 * backtracking. *)
let eval_expr last =
  vernac_com Vernacentries.interp last;
  Lib.add_frozen_state();
  Lib.mark_end_of_command()

(* raw_do_vernac : Pcoq.Gram.parsable -> unit
 * vernac_step . parse_sentence *)
let raw_do_vernac po = eval_expr (parse_sentence (po,None))

(* XML output hooks *)
let xml_start_library = ref (fun _ -> ())
let xml_end_library = ref (fun _ -> ())

let set_xml_start_library f = xml_start_library := f
let set_xml_end_library f = xml_end_library := f

(* Load a vernac file. Errors are annotated with file and location *)
let load_vernac verb file =
  chan_beautify :=
    if !Flags.beautify_file then open_out (file^beautify_suffix) else stdout;
  try
    read_vernac_file verb file;
    if !Flags.beautify_file then close_out !chan_beautify;
  with e ->
    if !Flags.beautify_file then close_out !chan_beautify;
    raise_with_file file e

(* Compile a vernac file (f is assumed without .v suffix) *)
let compile verbosely f =
  let ldir,long_f_dot_v = Flags.verbosely Library.start_library f in
    if Dumpglob.multi_dump () then
      Dumpglob.open_glob_file (f ^ ".glob");
    Dumpglob.dump_string ("F" ^ Names.string_of_dirpath ldir ^ "\n");
    if !Flags.xml_export then !xml_start_library ();
    let _ = load_vernac verbosely long_f_dot_v in
     if Pfedit.get_all_proof_names () <> [] then
	(message "Error: There are pending proofs"; exit 1);
      if !Flags.xml_export then !xml_end_library ();
      if Dumpglob.multi_dump () then Dumpglob.close_glob_file ();
      Library.save_library_to ldir (long_f_dot_v ^ "o")


