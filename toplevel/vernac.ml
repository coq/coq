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
open Vernacprop

(* The functions in this module may raise (unexplainable!) exceptions.
   Use the module Coqtoplevel, which catches these exceptions
   (the exceptions are explained only at the toplevel). *)

let checknav_simple (loc, cmd) =
  if is_navigation_vernac cmd && not (is_reset cmd) then
    CErrors.user_err ?loc (str "Navigation commands forbidden in files.")

let checknav_deep (loc, ast) =
  if is_deep_navigation_vernac ast then
    CErrors.user_err ?loc (str "Navigation commands forbidden in nested commands.")


let disable_drop = function
  | Drop -> CErrors.error "Drop is forbidden."
  | e -> e

(* Echo from a buffer based on position.
   XXX: Should move to utility file. *)
let vernac_echo ?loc in_chan = let open Loc in
  Option.iter (fun loc ->
      let len = loc.ep - loc.bp in
      seek_in in_chan loc.bp;
      Feedback.msg_notice @@ str @@ really_input_string in_chan len
    ) loc

(* vernac parses the given stream, executes interpfun on the syntax tree it
 * parses, and is verbose on "primitives" commands if verbosely is true *)

let beautify_suffix = ".beautified"

let set_formatter_translator ch =
  let out s b e = output_substring ch s b e in
  Format.set_formatter_output_functions out (fun () -> flush ch);
  Format.set_max_boxes max_int

let pr_new_syntax_in_context ?loc chan_beautify ocom =
  let loc = Option.cata Loc.unloc (0,0) loc in
  if !beautify_file then set_formatter_translator chan_beautify;
  let fs = States.freeze ~marshallable:`No in
  (* The content of this is not supposed to fail, but if ever *)
  try
    (* Side-effect: order matters *)
    let before = comment (CLexer.extract_comments (fst loc)) in
    let com = match ocom with
      | Some com -> Ppvernac.pr_vernac com
      | None -> mt() in
    let after = comment (CLexer.extract_comments (snd loc)) in
    if !beautify_file then
      (Pp.pp_with !Topfmt.std_ft (hov 0 (before ++ com ++ after));
       Format.pp_print_flush !Topfmt.std_ft ())
    else
      Feedback.msg_info (hov 4 (str"New Syntax:" ++ fnl() ++ (hov 0 com)));
    States.unfreeze fs;
    Format.set_formatter_out_channel stdout
  with any ->
    States.unfreeze fs;
    Format.set_formatter_out_channel stdout

let pr_new_syntax ?loc po chan_beautify ocom =
  (* Reinstall the context of parsing which includes the bindings of comments to locations *)
  Pcoq.Gram.with_parsable po (pr_new_syntax_in_context ?loc chan_beautify) ocom

(* For coqtop -time, we display the position in the file,
   and a glimpse of the executed command *)

let pp_cmd_header ?loc com =
  let shorten s =
    if Unicode.utf8_length s > 33 then (Unicode.utf8_sub s 0 30) ^ "..." else s
  in
  let noblank s = String.map (fun c ->
      match c with
	| ' ' | '\n' | '\t' | '\r' -> '~'
	| x -> x
      ) s
  in
  let (start,stop) = Option.cata Loc.unloc (0,0) loc in
  let safe_pr_vernac x =
    try Ppvernac.pr_vernac x
    with e -> str (Printexc.to_string e) in
  let cmd = noblank (shorten (string_of_ppcmds (safe_pr_vernac com)))
  in str "Chars " ++ int start ++ str " - " ++ int stop ++
     str " [" ++ str cmd ++ str "] "

(* This is a special case where we assume we are in console batch mode
   and take control of the console.
 *)
let print_cmd_header ?loc com =
  Pp.pp_with !Topfmt.std_ft (pp_cmd_header ?loc com);
  Format.pp_print_flush !Topfmt.std_ft ()

let pr_open_cur_subgoals () =
  try Printer.pr_open_subgoals ()
  with Proof_global.NoCurrentProof -> Pp.str ""

let vernac_error msg =
  Format.fprintf !Topfmt.err_ft "@[%a@]%!" Pp.pp_with msg;
  flush_all ();
  exit 1

(* Reenable when we get back to feedback printing *)
(* let is_end_of_input any = match any with *)
(*     Stm.End_of_input -> true *)
(*   | _ -> false *)

let rec interp_vernac sid (loc,com) =
  let interp = function
    | VernacLoad (verbosely, fname) ->
	let fname = Envars.expand_path_macros ~warn:(fun x -> Feedback.msg_warning (str x)) fname in
        let fname = CUnix.make_suffix fname ".v" in
        let f = Loadpath.locate_file fname in
        load_vernac verbosely sid f
    | v ->

      (* XXX: We need to run this before add as the classification is
         highly dynamic and depends on the structure of the
         document. Hopefully this is fixed when VtBack can be removed
         and Undo etc... are just interpreted regularly. *)
      let is_proof_step = match fst (Vernac_classifier.classify_vernac v) with
        | VtProofStep _ | VtStm (VtBack _, _) | VtStartProof _ -> true
        | _ -> false
      in

      let nsid, ntip = Stm.add ~ontop:sid (not !Flags.quiet) (loc,v) in

      (* Main STM interaction *)
      if ntip <> `NewTip then
        anomaly (str "vernac.ml: We got an unfocus operation on the toplevel!");
      (* Due to bug #5363 we cannot use observe here as we should,
         it otherwise reveals bugs *)
      (* Stm.observe nsid; *)

      let check_proof = Flags.(!compilation_mode = BuildVo || not !batch_mode) in
      if check_proof then Stm.finish ();

      (* We could use a more refined criteria that depends on the
         vernac. For now we imitate the old approach and rely on the
         classification. *)
      let print_goals = not !Flags.batch_mode && not !Flags.quiet &&
                        is_proof_step && Proof_global.there_are_pending_proofs () in

      if print_goals then Feedback.msg_notice (pr_open_cur_subgoals ());
      nsid
  in
    try
      (* The -time option is only supported from console-based
         clients due to the way it prints. *)
      if !Flags.time then print_cmd_header ?loc com;
      let com = if !Flags.time then VernacTime (loc,com) else com in
      interp com
    with reraise ->
      (* XXX: In non-interactive mode edit_at seems to do very weird
         things, so we better avoid it while we investigate *)
      if not !Flags.batch_mode then ignore(Stm.edit_at sid);
      let (reraise, info) = CErrors.push reraise in
      let info = begin
        match Loc.get_loc info with
        | None   -> Option.cata (Loc.add_loc info) info loc
        | Some _ -> info
      end in iraise (reraise, info)

(* Load a vernac file. CErrors are annotated with file and location *)
and load_vernac verbosely sid file =
  let chan_beautify =
    if !Flags.beautify_file then open_out (file^beautify_suffix) else stdout in
  let in_chan = open_utf8_file_in file in
  let in_echo = if verbosely then Some (open_utf8_file_in file) else None in
  let in_pa   = Pcoq.Gram.parsable ~file (Stream.of_channel in_chan) in
  let rsid = ref sid in
  try
    (* we go out of the following infinite loop when a End_of_input is
     * raised, which means that we raised the end of the file being loaded *)
    while true do
      let loc, ast =
          Stm.parse_sentence !rsid in_pa
        (* If an error in parsing occurs, we propagate the exception
           so the caller of load_vernac will take care of it. However,
           in the future it could be possible that we want to handle
           all the errors as feedback events, thus in this case we
           should relay the exception here for convenience. A
           possibility is shown below, however we may want to refactor
           this code:

        try Stm.parse_sentence !rsid in_pa
        with
        | any when not is_end_of_input any ->
          let (e, info) = CErrors.push any in
          let loc = Loc.get_loc info in
          let msg = CErrors.iprint (e, info) in
          Feedback.msg_error ?loc msg;
          iraise (e, info)
       *)
      in
      (* Printing of vernacs *)
      if !beautify then pr_new_syntax ?loc in_pa chan_beautify (Some ast);
      Option.iter (vernac_echo ?loc) in_echo;

      checknav_simple (loc, ast);
      let nsid = Flags.silently (interp_vernac !rsid) (loc, ast) in
      rsid := nsid
    done;
    !rsid
  with any ->   (* whatever the exception *)
    let (e, info) = CErrors.push any in
    close_in in_chan;
    Option.iter close_in in_echo;
    match e with
      | Stm.End_of_input ->
          (* Is this called so comments at EOF are printed? *)
          if !beautify then
            pr_new_syntax ~loc:(Loc.make_loc (max_int,max_int)) in_pa chan_beautify None;
          if !Flags.beautify_file then close_out chan_beautify;
          !rsid
      | reraise ->
         if !Flags.beautify_file then close_out chan_beautify;
	 iraise (disable_drop e, info)

(** [eval_expr : ?preserving:bool -> Loc.t * Vernacexpr.vernac_expr -> unit]
   It executes one vernacular command. By default the command is
   considered as non-state-preserving, in which case we add it to the
   Backtrack stack (triggering a save of a frozen state and the generation
   of a new state label). An example of state-preserving command is one coming
   from the query panel of Coqide. *)

let process_expr sid loc_ast =
  checknav_deep loc_ast;
  interp_vernac sid loc_ast

(* XML output hooks *)
let (f_xml_start_library, xml_start_library) = Hook.make ~default:ignore ()
let (f_xml_end_library, xml_end_library) = Hook.make ~default:ignore ()

let warn_file_no_extension =
  CWarnings.create ~name:"file-no-extension" ~category:"filesystem"
         (fun (f,ext) ->
          str "File \"" ++ str f ++
            strbrk "\" has been implicitly expanded to \"" ++
            str f ++ str ext ++ str "\"")

let ensure_ext ext f =
  if Filename.check_suffix f ext then f
  else begin
    warn_file_no_extension (f,ext);
    f ^ ext
  end

let chop_extension f =
  try Filename.chop_extension f with _ -> f

let ensure_bname src tgt =
  let src, tgt = Filename.basename src, Filename.basename tgt in
  let src, tgt = chop_extension src, chop_extension tgt in
  if src <> tgt then
    vernac_error (str "Source and target file names must coincide, directories can differ" ++ fnl () ++
                  str "Source: " ++ str src                                                ++ fnl () ++
                  str "Target: " ++ str tgt)

let ensure ext src tgt = ensure_bname src tgt; ensure_ext ext tgt

let ensure_v v = ensure ".v" v v
let ensure_vo v vo = ensure ".vo" v vo
let ensure_vio v vio = ensure ".vio" v vio

let ensure_exists f =
  if not (Sys.file_exists f) then
    vernac_error (hov 0 (str "Can't find file" ++ spc () ++ str f))

(* Compile a vernac file *)
let compile verbosely f =
  let check_pending_proofs () =
    let pfs = Pfedit.get_all_proof_names () in
    if not (List.is_empty pfs) then vernac_error (str "There are pending proofs")
  in
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
      Dumpglob.start_dump_glob ~vfile:long_f_dot_v ~vofile:long_f_dot_vo;
      Dumpglob.dump_string ("F" ^ Names.DirPath.to_string ldir ^ "\n");
      if !Flags.xml_export then Hook.get f_xml_start_library ();
      let wall_clock1 = Unix.gettimeofday () in
      let _ = load_vernac verbosely (Stm.get_current_state ()) long_f_dot_v in
      Stm.join ();
      let wall_clock2 = Unix.gettimeofday () in
      check_pending_proofs ();
      Library.save_library_to ldir long_f_dot_vo (Global.opaque_tables ());
      Aux_file.record_in_aux_at "vo_compile_time"
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
      let _ = load_vernac verbosely (Stm.get_current_state ()) long_f_dot_v in
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
