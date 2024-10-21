(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Parsing of vernacular. *)

open Pp
open CErrors
open Util
open Vernacexpr
open Vernacprop

(* The functions in this module may raise (unexplainable!) exceptions.
   Use the module Coqtoplevel, which catches these exceptions
   (the exceptions are explained only at the toplevel). *)

let checknav { CAst.loc; v = { expr } }  =
  if is_navigation_vernac expr && not (is_reset expr) then
    CErrors.user_err ?loc (str "Navigation commands forbidden in files.")

(* Echo from a buffer based on position.
   XXX: Should move to utility file. *)
let vernac_echo ?loc in_chan = let open Loc in
  Option.iter (fun loc ->
      let len = loc.ep - loc.bp in
      seek_in in_chan loc.bp;
      Feedback.msg_notice @@ str @@ really_input_string in_chan len
    ) loc


type time_output =
  | ToFeedback
  | ToChannel of Format.formatter

let make_time_output = function
  | Coqargs.ToFeedback -> ToFeedback
  | ToFile f ->
    let ch = open_out f in
    let fch = Format.formatter_of_out_channel ch in
    let close () =
      Format.pp_print_flush fch ();
      close_out ch
    in
    at_exit close;
    ToChannel fch

module State = struct

  type t = {
    doc : Stm.doc;
    sid : Stateid.t;
    proof : Proof.t option;
    time : time_output option;
  }

end

let emit_time state com tstart tend =
  match state.State.time with
  | None -> ()
  | Some time ->
    let pp = Topfmt.pr_cmd_header com ++ System.fmt_time_difference tstart tend in
    match time with
    | ToFeedback -> Feedback.msg_notice pp
    | ToChannel ch -> Pp.pp_with ch (pp ++ fnl())

let interp_vernac ~check ~state ({CAst.loc;_} as com) =
  let open State in
    try
      let doc, nsid, ntip = Stm.add ~doc:state.doc ~ontop:state.sid (not !Flags.quiet) com in

      (* Main STM interaction *)
      if ntip <> Stm.NewAddTip then
        anomaly (str "vernac.ml: We got an unfocus operation on the toplevel!");

      (* Force the command  *)
      let () = if check then Stm.observe ~doc nsid in
      let new_proof = Vernacstate.Declare.give_me_the_proof_opt () [@ocaml.warning "-3"] in
      { state with doc; sid = nsid; proof = new_proof; }
    with reraise ->
      let (reraise, info) = Exninfo.capture reraise in
      let info =
        (* Set the loc to the whole command if no loc *)
        match Loc.get_loc info, loc with
        | None, Some loc -> Loc.add_loc info loc
        | Some _, _ | _, None  -> info
      in
      Exninfo.iraise (reraise, info)

(* Load a vernac file. CErrors are annotated with file and location *)
let load_vernac_core ~echo ~check ~state ?source file =
  (* Keep in sync *)
  let in_chan = open_utf8_file_in file in
  let in_echo = if echo then Some (open_utf8_file_in file) else None in
  let input_cleanup () = close_in in_chan; Option.iter close_in in_echo in

  let source = Option.default (Loc.InFile {dirpath=None; file}) source in
  let in_pa = Procq.Parsable.make ~loc:Loc.(initial source)
      (Gramlib.Stream.of_channel in_chan) in
  let open State in

  (* ids = For beautify, list of parsed sids *)
  let rec loop state ids =
    let tstart = System.get_time () in
    match
      NewProfile.profile "parse_command" (fun () ->
          Stm.parse_sentence
            ~doc:state.doc ~entry:Pvernac.main_entry state.sid in_pa)
        ()
    with
    | None ->
      input_cleanup ();
      state, ids, Procq.Parsable.comments in_pa
    | Some ast ->
      (* Printing of AST for -compile-verbose *)
      Option.iter (vernac_echo ?loc:ast.CAst.loc) in_echo;

      checknav ast;

      let state =
        try_finally
          (fun () ->
             NewProfile.profile "command"
               ~args:(fun () ->
                   let lnum = match ast.loc with
                     | None -> "unknown"
                     | Some loc -> string_of_int loc.line_nb
                   in
                   [("cmd", `String (Pp.string_of_ppcmds (Topfmt.pr_cmd_header ast)));
                    ("line", `String lnum)])
               (fun () ->
             Flags.silently (interp_vernac ~check ~state) ast) ())
          ()
          (fun () ->
             let tend = System.get_time () in
             (* The -time option is only supported from console-based clients
                due to the way it prints. *)
             emit_time state ast tstart tend)
          ()
      in

      (loop [@ocaml.tailcall]) state (state.sid :: ids)
  in
  try loop state []
  with any ->   (* whatever the exception *)
    let (e, info) = Exninfo.capture any in
    input_cleanup ();
    Exninfo.iraise (e, info)

let process_expr ~state loc_ast =
  try interp_vernac ~check:true ~state loc_ast
  with reraise ->
    let reraise, info = Exninfo.capture reraise in

    (* Exceptions don't carry enough state to print themselves (typically missing the nametab)
       so we need to print before resetting to an older state. See eg #16745 *)
    let reraise = UserError (CErrors.iprint (reraise, info)) in
    (* Keep just the loc in the info as it's printed separately *)
    let info = Option.cata (Loc.add_loc Exninfo.null) Exninfo.null (Loc.get_loc info) in

    ignore(Stm.edit_at ~doc:state.doc state.sid);
    Exninfo.iraise (reraise, info)

let process_expr ~state loc_ast =
  let tstart = System.get_time () in
  try_finally (fun () -> process_expr ~state loc_ast)
    ()
    (fun () ->
       let tend = System.get_time () in
       emit_time state loc_ast tstart tend)
    ()

(******************************************************************************)
(* Beautify-specific code                                                     *)
(******************************************************************************)

(* vernac parses the given stream, executes interpfun on the syntax tree it
 * parses, and is verbose on "primitives" commands if verbosely is true *)
let beautify_suffix = ".beautified"

let set_formatter_translator ch =
  let out s b e = output_substring ch s b e in
  let ft = Format.make_formatter out (fun () -> flush ch) in
  Format.pp_set_max_boxes ft max_int;
  ft

let pr_new_syntax ?loc ft_beautify ocom =
  let loc = Option.append loc (Option.bind ocom (fun x -> x.CAst.loc)) in
  let loc = Option.cata Loc.unloc (0,0) loc in
  let before = comment (Pputils.extract_comments (fst loc)) in
  let com = Option.cata (fun com -> Ppvernac.pr_vernac com ++ fnl()) (mt ()) ocom in
  let after = comment (Pputils.extract_comments (snd loc)) in
  if !Flags.beautify_file then
    (Pp.pp_with ft_beautify (hov 0 (before ++ com ++ after));
     Format.pp_print_flush ft_beautify ())
  else
    Feedback.msg_info (hov 4 (str"New Syntax:" ++ fnl() ++ (hov 0 com)))

(* load_vernac with beautify *)
let beautify_pass ~doc ~comments ~ids ~filename =
  let ft_beautify, close_beautify =
    if !Flags.beautify_file then
      let chan_beautify = open_out (filename^beautify_suffix) in
      set_formatter_translator chan_beautify, fun () -> close_out chan_beautify;
    else
      !Topfmt.std_ft, fun () -> ()
  in
  (* The interface to the comment printer is imperative, so we first
     set the comments, then we call print. This has to be done for
     each file. *)
  Pputils.beautify_comments := comments;
  List.iter (fun id -> pr_new_syntax ft_beautify (Stm.get_ast ~doc id)) ids;

  (* Is this called so comments at EOF are printed? *)
  pr_new_syntax ~loc:(Loc.make_loc (max_int,max_int)) ft_beautify None;
  close_beautify ()

(* Main driver for file loading. For now, we only do one beautify
   pass. *)
let load_vernac ~echo ~check ~state ?source filename =
  let ostate, ids, comments = load_vernac_core ~echo ~check ~state ?source filename in
  (* Pass for beautify *)
  if !Flags.beautify then beautify_pass ~doc:ostate.State.doc ~comments ~ids:(List.rev ids) ~filename;
  (* End pass *)
  ostate
