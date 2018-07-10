(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

let checknav_simple {CAst.loc;v=cmd} =
  if is_navigation_vernac cmd && not (is_reset cmd) then
    CErrors.user_err ?loc (str "Navigation commands forbidden in files.")

let checknav_deep {CAst.loc;v=ast} =
  if is_deep_navigation_vernac ast then
    CErrors.user_err ?loc (str "Navigation commands forbidden in nested commands.")

(* Echo from a buffer based on position.
   XXX: Should move to utility file. *)
let vernac_echo ?loc in_chan = let open Loc in
  Option.iter (fun loc ->
      let len = loc.ep - loc.bp in
      seek_in in_chan loc.bp;
      Feedback.msg_notice @@ str @@ really_input_string in_chan len
    ) loc

(* For coqtop -time, we display the position in the file,
   and a glimpse of the executed command *)

let pp_cmd_header {CAst.loc;v=com} =
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
let print_cmd_header com =
  Pp.pp_with !Topfmt.std_ft (pp_cmd_header com);
  Format.pp_print_flush !Topfmt.std_ft ()

(* Reenable when we get back to feedback printing *)
(* let is_end_of_input any = match any with *)
(*     Stm.End_of_input -> true *)
(*   | _ -> false *)

module State = struct

  type t = {
    doc : Stm.doc;
    sid : Stateid.t;
    proof : Proof.t option;
    time : bool;
  }

end

let interp_vernac ~check ~interactive ~state ({CAst.loc;_} as com) =
  let open State in
    try
      (* The -time option is only supported from console-based clients
         due to the way it prints. *)
      let com = if state.time
        then begin
          print_cmd_header com;
          CAst.make ?loc @@ VernacTime(state.time,com)
        end else com in
      let doc, nsid, ntip = Stm.add ~doc:state.doc ~ontop:state.sid (not !Flags.quiet) com in

      (* Main STM interaction *)
      if ntip <> `NewTip then
        anomaly (str "vernac.ml: We got an unfocus operation on the toplevel!");

      (* Due to bug #5363 we cannot use observe here as we should,
         it otherwise reveals bugs *)
      (* Stm.observe nsid; *)
      let ndoc = if check then Stm.finish ~doc else doc in
      let new_proof = Proof_global.give_me_the_proof_opt () in
      { state with doc = ndoc; sid = nsid; proof = new_proof; }
    with reraise ->
      (* XXX: In non-interactive mode edit_at seems to do very weird
         things, so we better avoid it while we investigate *)
      if interactive then ignore(Stm.edit_at ~doc:state.doc state.sid);
      let (reraise, info) = CErrors.push reraise in
      let info = begin
        match Loc.get_loc info with
        | None   -> Option.cata (Loc.add_loc info) info loc
        | Some _ -> info
      end in iraise (reraise, info)

(* Load a vernac file. CErrors are annotated with file and location *)
let load_vernac_core ~echo ~check ~interactive ~state file =
  (* Keep in sync *)
  let in_chan = open_utf8_file_in file in
  let in_echo = if echo then Some (open_utf8_file_in file) else None in
  let input_cleanup () = close_in in_chan; Option.iter close_in in_echo in

  let in_pa   = Pcoq.Parsable.make ~file:(Loc.InFile file) (Stream.of_channel in_chan) in
  let rstate  = ref state in
  (* For beautify, list of parsed sids *)
  let rids    = ref [] in
  let open State in
  try
    (* we go out of the following infinite loop when a End_of_input is
     * raised, which means that we raised the end of the file being loaded *)
    while true do
      let { CAst.loc; _ } as ast =
          Stm.parse_sentence ~doc:!rstate.doc !rstate.sid in_pa
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
      Option.iter (vernac_echo ?loc) in_echo;

      checknav_simple ast;
      let state = Flags.silently (interp_vernac ~check ~interactive ~state:!rstate) ast in
      rids := state.sid :: !rids;
      rstate := state;
    done;
    input_cleanup ();
    !rstate, !rids, Pcoq.Parsable.comment_state in_pa
  with any ->   (* whatever the exception *)
    let (e, info) = CErrors.push any in
    input_cleanup ();
    match e with
    | Stm.End_of_input -> !rstate, !rids, Pcoq.Parsable.comment_state in_pa
    | reraise -> iraise (e, info)

let process_expr ~state loc_ast =
  checknav_deep loc_ast;
  interp_vernac ~interactive:true ~check:true ~state loc_ast

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
  let loc = Option.cata Loc.unloc (0,0) loc in
  let before = comment (Pputils.extract_comments (fst loc)) in
  let com = Option.cata Ppvernac.pr_vernac (mt ()) ocom in
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
  List.iter (fun id ->
      Option.iter (fun (loc,ast) ->
          pr_new_syntax ?loc ft_beautify (Some ast))
        (Stm.get_ast ~doc id)) ids;

  (* Is this called so comments at EOF are printed? *)
  pr_new_syntax ~loc:(Loc.make_loc (max_int,max_int)) ft_beautify None;
  close_beautify ()

(* Main driver for file loading. For now, we only do one beautify
   pass. *)
let load_vernac ~echo ~check ~interactive ~state filename =
  let ostate, ids, comments = load_vernac_core ~echo ~check ~interactive ~state filename in
  (* Pass for beautify *)
  if !Flags.beautify then beautify_pass ~doc:ostate.State.doc ~comments ~ids:List.(rev ids) ~filename;
  (* End pass *)
  ostate
