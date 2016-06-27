(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Parsing of vernacular. *)

open Pp
open CErrors
open Util
open Flags
open Vernacexpr

(* The functions in this module may raise (unexplainable!) exceptions.
   Use the module Coqtoplevel, which catches these exceptions
   (the exceptions are explained only at the toplevel). *)

(* The navigation vernac commands will be handled separately *)

let rec is_navigation_vernac = function
  | VernacResetInitial
  | VernacResetName _
  | VernacBacktrack _
  | VernacBackTo _
  | VernacBack _ -> true
  | VernacRedirect (_, (_,c))
  | VernacTime (_,c) ->
      is_navigation_vernac c (* Time Back* is harmless *)
  | c -> is_deep_navigation_vernac c

and is_deep_navigation_vernac = function
  | VernacTimeout (_,c) | VernacFail c -> is_navigation_vernac c
  | _ -> false

(* NB: Reset is now allowed again as asked by A. Chlipala *)

let is_reset = function
  | VernacResetInitial | VernacResetName _ -> true
  | _ -> false

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

let disable_drop = function
  | Drop -> CErrors.error "Drop is forbidden."
  | e -> e

let user_error loc s = CErrors.user_err_loc (loc,"_",str s)

(* Opening and closing a channel. Open it twice when verbose: the first
   channel is used to read the commands, and the second one to print them.
   Note: we could use only one thanks to seek_in, but seeking on and on in
   the file we parse seems a bit risky to me.  B.B.  *)

let open_file_twice_if verbosely longfname =
  let in_chan = open_utf8_file_in longfname in
  let verb_ch =
    if verbosely then Some (open_utf8_file_in longfname) else None in
  CLexer.set_current_file longfname;
  let po = Pcoq.Gram.parsable (Stream.of_channel in_chan) in
  (in_chan, longfname, (po, verb_ch))

let close_input in_chan (_,verb) =
  try
    close_in in_chan;
    match verb with
      | Some verb_ch -> close_in verb_ch
      | _ -> ()
  with e when CErrors.noncritical e -> ()

let verbose_phrase verbch loc =
  let loc = Loc.unloc loc in
  match verbch with
    | Some ch ->
	let len = snd loc - fst loc in
	let s = String.create len in
        seek_in ch (fst loc);
        really_input ch s 0 len;
        Feedback.msg_notice (str s ++ fnl ())
    | None -> ()

exception End_of_input

let parse_sentence = Flags.with_option Flags.we_are_parsing
  (fun (po, verbch) ->
  match Pcoq.Gram.entry_parse Pcoq.main_entry po with
    | Some (loc,_ as com) -> verbose_phrase verbch loc; com
    | None -> raise End_of_input)

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
  let fs = States.freeze ~marshallable:`No in
  let com = match ocom with
    | Some com -> Ppvernac.pr_vernac com
    | None -> mt() in
  if !beautify_file then
    Feedback.msg_notice (hov 0 (comment (fst loc) ++ com ++ comment (snd loc)))
  else
    Feedback.msg_info (hov 4 (str"New Syntax:" ++ fnl() ++ (hov 0 com)));
  States.unfreeze fs;
  Format.set_formatter_out_channel stdout

let save_translator_coqdoc () =
  (* translator state *)
  let ch = !chan_beautify in
  let cl = !Pp.comments in
  let cs = CLexer.com_state() in
  (* end translator state *)
  let coqdocstate = CLexer.location_table () in
  ch,cl,cs,coqdocstate

let restore_translator_coqdoc (ch,cl,cs,coqdocstate) =
  if !Flags.beautify_file then close_out !chan_beautify;
  chan_beautify := ch;
  Pp.comments := cl;
  CLexer.restore_com_state cs;
  CLexer.restore_location_table coqdocstate

(* For coqtop -time, we display the position in the file,
   and a glimpse of the executed command *)

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
  let safe_pr_vernac x =
    try Ppvernac.pr_vernac x
    with e -> str (Printexc.to_string e) in
  let cmd = noblank (shorten (string_of_ppcmds (safe_pr_vernac com)))
  in
  Feedback.msg_notice
    (str "Chars " ++ int start ++ str " - " ++ int stop ++
     str " [" ++ str cmd ++ str "] ")


let rec vernac_com verbose checknav (loc,com) =
  let interp = function
    | VernacLoad (verbosely, fname) ->
	let fname = Envars.expand_path_macros ~warn:(fun x -> Feedback.msg_warning (str x)) fname in
        let fname = CUnix.make_suffix fname ".v" in
        let f = Loadpath.locate_file fname in
	let st = save_translator_coqdoc () in
	if !Flags.beautify_file then
	  begin
	    chan_beautify := open_out (f^beautify_suffix);
	    Pp.comments := []
          end;
	begin
	  try
            read_vernac_file verbosely f;
	    restore_translator_coqdoc st;
	  with reraise ->
            let reraise = CErrors.push reraise in
	    restore_translator_coqdoc st;
	    iraise reraise
	end

    | v when !just_parsing -> ()

    | v -> Stm.interp verbose (loc,v)
  in
    try
      checknav loc com;
      if do_beautify () then pr_new_syntax loc (Some com);
      if !Flags.time then display_cmd_header loc com;
      let com = if !Flags.time then VernacTime (loc,com) else com in
      let a = CLexer.com_state () in
      interp com;
      CLexer.restore_com_state a
    with reraise ->
      let (reraise, info) = CErrors.push reraise in
      Format.set_formatter_out_channel stdout;
      let loc' = Option.default Loc.ghost (Loc.get_loc info) in
      if Loc.is_ghost loc' then iraise (reraise, Loc.add_loc info loc)
      else iraise (reraise, info)

and read_vernac_file verbosely s =
  let checknav loc cmd =
    if is_navigation_vernac cmd && not (is_reset cmd) then
	user_error loc "Navigation commands forbidden in files"
  in
  let (in_chan, fname, input) = open_file_twice_if verbosely s in
  try
    (* we go out of the following infinite loop when a End_of_input is
     * raised, which means that we raised the end of the file being loaded *)
    while true do
      let loc_ast = parse_sentence input in
      vernac_com verbosely checknav loc_ast
    done
  with any ->   (* whatever the exception *)
    let (e, info) = CErrors.push any in
    Format.set_formatter_out_channel stdout;
    close_input in_chan input;    (* we must close the file first *)
    match e with
      | End_of_input ->
          if do_beautify () then
            pr_new_syntax (Loc.make_loc (max_int,max_int)) None
      | reraise ->
	 iraise (disable_drop e, info)

(** [eval_expr : ?preserving:bool -> Loc.t * Vernacexpr.vernac_expr -> unit]
   It executes one vernacular command. By default the command is
   considered as non-state-preserving, in which case we add it to the
   Backtrack stack (triggering a save of a frozen state and the generation
   of a new state label). An example of state-preserving command is one coming
   from the query panel of Coqide. *)

let checknav loc ast =
  if is_deep_navigation_vernac ast then
    user_error loc "Navigation commands forbidden in nested commands"

let eval_expr loc_ast = vernac_com (Flags.is_verbose()) checknav loc_ast

(* XML output hooks *)
let (f_xml_start_library, xml_start_library) = Hook.make ~default:ignore ()
let (f_xml_end_library, xml_end_library) = Hook.make ~default:ignore ()

(* Load a vernac file. CErrors are annotated with file and location *)
let load_vernac verb file =
  chan_beautify :=
    if !Flags.beautify_file then open_out (file^beautify_suffix) else stdout;
  try
    Flags.silently (read_vernac_file verb) file;
    if !Flags.beautify_file then close_out !chan_beautify;
  with any ->
    let (e, info) = CErrors.push any in
    if !Flags.beautify_file then close_out !chan_beautify;
    iraise (disable_drop e, info)

let ensure_ext ext f =
  if Filename.check_suffix f ext then f
  else begin
    Feedback.msg_warning (str "File \"" ++ str f ++ strbrk "\" has been implicitly \
    expanded to \"" ++ str f ++ str ext ++ str "\"");
    f ^ ext
  end

let chop_extension f =
  try Filename.chop_extension f with _ -> f

let ensure_bname src tgt =
  let src, tgt = Filename.basename src, Filename.basename tgt in
  let src, tgt = chop_extension src, chop_extension tgt in
  if src <> tgt then begin
    Feedback.msg_error (str "Source and target file names must coincide, directories can differ");
    Feedback.msg_error (str "Source: " ++ str src);
    Feedback.msg_error (str "Target: " ++ str tgt);
    flush_all ();
    exit 1
  end

let ensure ext src tgt = ensure_bname src tgt; ensure_ext ext tgt

let ensure_v v = ensure ".v" v v
let ensure_vo v vo = ensure ".vo" v vo
let ensure_vio v vio = ensure ".vio" v vio

let ensure_exists f =
  if not (Sys.file_exists f) then begin
    Feedback.msg_error (hov 0 (str "Can't find file" ++ spc () ++ str f));
    exit 1
  end

(* Compile a vernac file *)
let compile verbosely f =
  let check_pending_proofs () =
    let pfs = Pfedit.get_all_proof_names () in
    if not (List.is_empty pfs) then
      (Feedback.msg_error (str "There are pending proofs"); flush_all (); exit 1) in
  match !Flags.compilation_mode with
  | BuildVo ->
      let long_f_dot_v = ensure_v f in
      ensure_exists long_f_dot_v;
      let long_f_dot_vo =
        match !Flags.compilation_output_name with
        | None -> long_f_dot_v ^ "o"
        | Some f -> ensure_vo long_f_dot_v f in
      let ldir = Flags.verbosely Library.start_library long_f_dot_vo in
      Stm.set_compilation_hints long_f_dot_vo;
      Aux_file.(start_aux_file
        ~aux_file:(aux_file_name_for long_f_dot_vo)
        ~v_file:long_f_dot_v);
      Dumpglob.start_dump_glob long_f_dot_v;
      Dumpglob.dump_string ("F" ^ Names.DirPath.to_string ldir ^ "\n");
      if !Flags.xml_export then Hook.get f_xml_start_library ();
      let wall_clock1 = Unix.gettimeofday () in
      let _ = load_vernac verbosely long_f_dot_v in
      Stm.join ();
      let wall_clock2 = Unix.gettimeofday () in
      check_pending_proofs ();
      Library.save_library_to ldir long_f_dot_vo (Global.opaque_tables ());
      Aux_file.record_in_aux_at Loc.ghost "vo_compile_time"
        (Printf.sprintf "%.3f" (wall_clock2 -. wall_clock1));
      Aux_file.stop_aux_file ();
      if !Flags.xml_export then Hook.get f_xml_end_library ();
      Dumpglob.end_dump_glob ()
  | BuildVio ->
      let long_f_dot_v = ensure_v f in
      ensure_exists long_f_dot_v;
      let long_f_dot_vio =
        match !Flags.compilation_output_name with
        | None -> long_f_dot_v ^ "io"
        | Some f -> ensure_vio long_f_dot_v f in
      let ldir = Flags.verbosely Library.start_library long_f_dot_vio in
      Dumpglob.noglob ();
      Stm.set_compilation_hints long_f_dot_vio;
      let _ = load_vernac verbosely long_f_dot_v in
      Stm.finish ();
      check_pending_proofs ();
      Stm.snapshot_vio ldir long_f_dot_vio;
      Stm.reset_task_queue ()
  | Vio2Vo ->
      let open Filename in
      let open Library in
      Dumpglob.noglob ();
      let f = if check_suffix f ".vio" then chop_extension f else f in
      let lfdv, sum, lib, univs, disch, tasks, proofs = load_library_todo f in
      Stm.set_compilation_hints lfdv;
      let univs, proofs = Stm.finish_tasks lfdv univs disch proofs tasks in
      Library.save_library_raw lfdv sum lib univs proofs

let compile v f = 
  ignore(CoqworkmgrApi.get 1);
  compile v f;
  CoqworkmgrApi.giveback 1

let () = Hook.set Stm.process_error_hook
  Cerrors.process_vernac_interp_error
