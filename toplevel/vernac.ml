(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Parsing of vernacular. *)

open Pp
open Errors
open Util
open Flags
open System
open Vernacexpr
open Vernacinterp

(* The functions in this module may raise (unexplainable!) exceptions.
   Use the module Coqtoplevel, which catches these exceptions
   (the exceptions are explained only at the toplevel). *)

exception DuringCommandInterp of Loc.t * exn

exception HasNotFailed

(* The navigation vernac commands will be handled separately *)

let rec is_navigation_vernac = function
  | VernacResetInitial
  | VernacResetName _
  | VernacBacktrack _
  | VernacBackTo _
  | VernacBack _ -> true
  | VernacTime c -> is_navigation_vernac c (* Time Back* is harmless *)
  | c -> is_deep_navigation_vernac c

and is_deep_navigation_vernac = function
  | VernacTimeout (_,c) | VernacFail c -> is_navigation_vernac c
  | VernacList l -> List.exists (fun (_,c) -> is_navigation_vernac c) l
  | _ -> false

(* NB: Reset is now allowed again as asked by A. Chlipala *)

let is_reset = function
  | VernacResetInitial | VernacResetName _ -> true
  | _ -> false

(* For coqtop -time, we display the position in the file,
   and a glimpse of the executed command *)

let time = ref false

let display_cmd_header loc com =
  let shorten s = try (String.sub s 0 30)^"..." with _ -> s in
  let noblank s =
    for i = 0 to String.length s - 1 do
      match s.[i] with
	| ' ' | '\n' | '\t' | '\r' -> s.[i] <- '~'
	| _ -> ()
    done;
    s
  in
  let (start,stop) = Loc.unloc loc in
  let cmd = noblank (shorten (string_of_ppcmds (Ppvernac.pr_vernac com)))
  in
  Pp.pp (str "Chars " ++ int start ++ str " - " ++ int stop ++
	 str (" ["^cmd^"] "));
  Pp.flush_all ()

(* When doing Load on a file, two behaviors are possible:

   - either the history stack is grown by only one command,
     the "Load" itself. This is mandatory for command-counting
     interfaces (CoqIDE).

   - either each individual sub-commands in the file is added
     to the history stack. This allows commands like Show Script
     to work across the loaded file boundary (cf. bug #2820).

   The best of the two could probably be combined someday,
   in the meanwhile we use a flag. *)

let atomic_load = ref true

let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = true;
      Goptions.optdepr  = false;
      Goptions.optname  = "atomic registration of commands in a Load";
      Goptions.optkey   = ["Atomic";"Load"];
      Goptions.optread  = (fun () -> !atomic_load);
      Goptions.optwrite = ((:=) atomic_load) }

(* Specifies which file is read. The intermediate file names are
   discarded here. The Drop exception becomes an error. We forget
   if the error ocurred during interpretation or not *)

let raise_with_file file exc =
  let (cmdloc,re) =
    match exc with
      | DuringCommandInterp(loc,e) -> (loc,e)
      | e -> (Loc.ghost,e)
  in
  let (inner,inex) =
    match re with
      | Error_in_file (_, (b,f,loc), e) when loc <> Loc.ghost ->
          ((b, f, loc), e)
      | Loc.Exc_located (loc, e) when loc <> Loc.ghost ->
          ((false,file, loc), e)
      | Loc.Exc_located (_, e) | e -> ((false,file,cmdloc), e)
  in
  raise (Error_in_file (file, inner, disable_drop inex))

let real_error = function
  | Loc.Exc_located (_, e) -> e
  | Error_in_file (_, _, e) -> e
  | e -> e

let user_error loc s = Errors.user_err_loc (loc,"_",str s)

(** Timeout handling *)

(** A global default timeout, controled by option "Set Default Timeout n".
    Use "Unset Default Timeout" to deactivate it (or set it to 0). *)

let default_timeout = ref None

let _ =
  Goptions.declare_int_option
    { Goptions.optsync  = true;
      Goptions.optdepr  = false;
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


(* Open an utf-8 encoded file and skip the byte-order mark if any *)

let open_utf8_file_in fname =
  let is_bom s =
    Int.equal (Char.code s.[0]) 0xEF &&
    Int.equal (Char.code s.[1]) 0xBB &&
    Int.equal (Char.code s.[2]) 0xBF
  in
  let in_chan = open_in fname in
  let s = "   " in
  if input in_chan s 0 3 < 3 || not (is_bom s) then seek_in in_chan 0;
  in_chan

(* Opening and closing a channel. Open it twice when verbose: the first
   channel is used to read the commands, and the second one to print them.
   Note: we could use only one thanks to seek_in, but seeking on and on in
   the file we parse seems a bit risky to me.  B.B.  *)

let open_file_twice_if verbosely fname =
  let paths = Library.get_load_paths () in
  let _,longfname =
    find_file_in_path ~warn:(Flags.is_verbose()) paths fname in
  let in_chan = open_utf8_file_in longfname in
  let verb_ch =
    if verbosely then Some (open_utf8_file_in longfname) else None in
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
  let loc = Loc.unloc loc in
  match verbch with
    | Some ch ->
	let len = snd loc - fst loc in
	let s = String.create len in
        seek_in ch (fst loc);
        really_input ch s 0 len;
        ppnl (str s);
        pp_flush()
    | None -> ()

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
  let loc = Loc.unloc loc in
  if !beautify_file then set_formatter_translator();
  let fs = States.freeze () in
  let com = match ocom with
    | Some VernacNop -> mt()
    | Some com -> Ppvernac.pr_vernac com
    | None -> mt() in
  if !beautify_file then
    pp (hov 0 (comment (fst loc) ++ com ++ comment (snd loc)))
  else
    msg_info (hov 4 (str"New Syntax:" ++ fnl() ++ (hov 0 com)));
  States.unfreeze fs;
  Format.set_formatter_out_channel stdout

let save_translator_coqdoc () =
  (* translator state *)
  let ch = !chan_beautify in
  let cl = !Pp.comments in
  let cs = Lexer.com_state() in
  (* end translator state *)
  let coqdocstate = Lexer.location_table () in
  ch,cl,cs,coqdocstate

let restore_translator_coqdoc (ch,cl,cs,coqdocstate) =
  if !Flags.beautify_file then close_out !chan_beautify;
  chan_beautify := ch;
  Pp.comments := cl;
  Lexer.restore_com_state cs;
  Lexer.restore_location_table coqdocstate

let rec vernac_com interpfun checknav (loc,com) =
  let rec interp = function
    | VernacLoad (verbosely, fname) ->
	let fname = Envars.expand_path_macros ~warn:(fun x -> msg_warning (str x)) fname in
	let st = save_translator_coqdoc () in
	if !Flags.beautify_file then
	  begin
            let _,f = find_file_in_path ~warn:(Flags.is_verbose())
	      (Library.get_load_paths ())
	      (CUnix.make_suffix fname ".v") in
	    chan_beautify := open_out (f^beautify_suffix);
	    Pp.comments := []
          end;
	begin
	  try
	    let status = read_vernac_file verbosely (CUnix.make_suffix fname ".v") in
	    restore_translator_coqdoc st;
            status
	  with e ->
	    restore_translator_coqdoc st;
	    raise e
	end

    | VernacList l ->
        List.fold_left (fun status (_,v) -> interp v && true) true l

    | v when !just_parsing -> true

    | VernacFail v ->
	begin try
	  (* If the command actually works, ignore its effects on the state *)
	  States.with_state_protection
	    (fun v -> ignore (interp v); raise HasNotFailed) v
	with e -> match real_error e with
	  | HasNotFailed ->
	      errorlabstrm "Fail" (str "The command has not failed !")
	  | e ->
	      (* Anomalies are re-raised by the next line *)
	      let msg = Errors.print_no_anomaly e in
	      if_verbose msg_info
		(str "The command has indeed failed with message:" ++
		 fnl () ++ str "=> " ++ hov 0 msg);
              true
	end

    | VernacTime v ->
	  let tstart = System.get_time() in
          let status = interp v in
	  let tend = System.get_time() in
	  let msg = if !time then "" else "Finished transaction in " in
          msg_info (str msg ++ System.fmt_time_difference tstart tend);
          status

    | VernacTimeout(n,v) ->
	  current_timeout := Some n;
	  interp v

    | v ->
	  let psh = default_set_timeout () in
	  try
            let status =
              States.with_heavy_rollback interpfun
                Cerrors.process_vernac_interp_error v
            in
	    restore_timeout psh;
            status
	  with e -> restore_timeout psh; raise e
  in
    try
      checknav loc com;
      current_timeout := !default_timeout;
      if do_beautify () then pr_new_syntax loc (Some com);
      if !time then display_cmd_header loc com;
      let com = if !time then VernacTime com else com in
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
  let checknav loc cmd =
    if is_navigation_vernac cmd && not (is_reset cmd) then
	user_error loc "Navigation commands forbidden in files"
  in
  let end_inner_command cmd =
    if !atomic_load || is_reset cmd then
      Lib.mark_end_of_command () (* for Reset in coqc or coqtop -l *)
    else
      Backtrack.mark_command cmd; (* for Show Script, cf bug #2820 *)
  in
  let (in_chan, fname, input) =
    open_file_twice_if verbosely s in
  let status = ref true in
  try
    (* we go out of the following infinite loop when a End_of_input is
     * raised, which means that we raised the end of the file being loaded *)
    while true do
      let loc_ast = parse_sentence input in
      let command_status = vernac_com interpfun checknav loc_ast in
      status := !status && command_status;
      end_inner_command (snd loc_ast);
      pp_flush ()
    done;
    assert false
  with e ->   (* whatever the exception *)
    Format.set_formatter_out_channel stdout;
    close_input in_chan input;    (* we must close the file first *)
    match real_error e with
      | End_of_input ->
          if do_beautify () then pr_new_syntax (Loc.make_loc (max_int,max_int)) None;
          !status
      | _ -> raise_with_file fname e

(** [eval_expr : ?preserving:bool -> Loc.t * Vernacexpr.vernac_expr -> unit]
   It executes one vernacular command. By default the command is
   considered as non-state-preserving, in which case we add it to the
   Backtrack stack (triggering a save of a frozen state and the generation
   of a new state label). An example of state-preserving command is one coming
   from the query panel of Coqide. *)

let checknav loc ast =
  if is_deep_navigation_vernac ast then
    user_error loc "Navigation commands forbidden in nested commands"

let eval_expr ?(preserving=false) loc_ast =
  let status = vernac_com Vernacentries.interp checknav loc_ast in
  if not preserving && not (is_navigation_vernac (snd loc_ast)) then
    Backtrack.mark_command (snd loc_ast);
  status

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
    Lib.mark_end_of_command (); (* in case we're still in coqtop init *)
    let _ = read_vernac_file verb file in
    if !Flags.beautify_file then close_out !chan_beautify;
  with e ->
    if !Flags.beautify_file then close_out !chan_beautify;
    raise_with_file file e

(* Compile a vernac file (f is assumed without .v suffix) *)
let compile verbosely f =
  let ldir,long_f_dot_v = Flags.verbosely Library.start_library f in
  Dumpglob.start_dump_glob long_f_dot_v;
  Dumpglob.dump_string ("F" ^ Names.string_of_dirpath ldir ^ "\n");
  if !Flags.xml_export then !xml_start_library ();
  let _ = load_vernac verbosely long_f_dot_v in
  if Pfedit.get_all_proof_names () <> [] then
    (pperrnl (str "Error: There are pending proofs"); flush_all (); exit 1);
  if !Flags.xml_export then !xml_end_library ();
  Dumpglob.end_dump_glob ();
  Library.save_library_to ldir (long_f_dot_v ^ "o")
