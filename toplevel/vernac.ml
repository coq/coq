(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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

let checknav_simple (loc, cmd) =
  if is_navigation_vernac cmd && not (is_reset cmd) then
    CErrors.user_err ?loc (str "Navigation commands forbidden in files.")

let checknav_deep (loc, ast) =
  if is_deep_navigation_vernac ast then
    CErrors.user_err ?loc (str "Navigation commands forbidden in nested commands.")


let disable_drop = function
  | Drop -> CErrors.user_err Pp.(str "Drop is forbidden.")
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
  let ft = Format.make_formatter out (fun () -> flush ch) in
  Format.pp_set_max_boxes ft max_int;
  ft

let pr_new_syntax_in_context ?loc ft_beautify ocom =
  let loc = Option.cata Loc.unloc (0,0) loc in
  let fs = States.freeze ~marshallable:`No in
  (* Side-effect: order matters *)
  let before = comment (CLexer.extract_comments (fst loc)) in
  let com = match ocom with
    | Some com -> Ppvernac.pr_vernac com
    | None -> mt() in
  let after = comment (CLexer.extract_comments (snd loc)) in
  if !Flags.beautify_file then
    (Pp.pp_with ft_beautify (hov 0 (before ++ com ++ after));
     Format.pp_print_flush ft_beautify ())
  else
    Feedback.msg_info (hov 4 (str"New Syntax:" ++ fnl() ++ (hov 0 com)));
  States.unfreeze fs

let pr_new_syntax ?loc po ft_beautify ocom =
  (* Reinstall the context of parsing which includes the bindings of comments to locations *)
  Pcoq.Gram.with_parsable po (pr_new_syntax_in_context ?loc ft_beautify) ocom

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
  try
    let proof = Proof_global.give_me_the_proof () in
    Printer.pr_open_subgoals ~proof
  with Proof_global.NoCurrentProof -> Pp.str ""

(* Reenable when we get back to feedback printing *)
(* let is_end_of_input any = match any with *)
(*     Stm.End_of_input -> true *)
(*   | _ -> false *)

let rec interp_vernac ~check ~interactive doc sid (loc,com) =
  let interp v =
    match under_control v with
    | VernacLoad (verbosely, fname) ->
        let fname = Envars.expand_path_macros ~warn:(fun x -> Feedback.msg_warning (str x)) fname in
        let fname = CUnix.make_suffix fname ".v" in
        let f = Loadpath.locate_file fname in
        load_vernac ~verbosely ~check ~interactive doc sid f
    | _ ->

      (* XXX: We need to run this before add as the classification is
         highly dynamic and depends on the structure of the
         document. Hopefully this is fixed when VtMeta can be removed
         and Undo etc... are just interpreted regularly. *)

      (* XXX: The classifier can emit warnings so we need to guard
         against that... *)
      let wflags = CWarnings.get_flags () in
      CWarnings.set_flags "none";
      let is_proof_step = match fst (Vernac_classifier.classify_vernac v) with
        | VtProofStep _ | VtMeta | VtStartProof _ -> true
        | _ -> false
      in
      CWarnings.set_flags wflags;

      let doc, nsid, ntip = Stm.add ~doc ~ontop:sid (not !Flags.quiet) (loc,v) in

      (* Main STM interaction *)
      if ntip <> `NewTip then
        anomaly (str "vernac.ml: We got an unfocus operation on the toplevel!");

      (* Due to bug #5363 we cannot use observe here as we should,
         it otherwise reveals bugs *)
      (* Stm.observe nsid; *)
      let ndoc = if check then Stm.finish ~doc else doc in

      (* We could use a more refined criteria that depends on the
         vernac. For now we imitate the old approach and rely on the
         classification. *)
      let print_goals = interactive && not !Flags.quiet &&
                        is_proof_step && Proof_global.there_are_pending_proofs () in

      if print_goals then Feedback.msg_notice (pr_open_cur_subgoals ());
      ndoc, nsid
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
      if interactive then ignore(Stm.edit_at ~doc sid);
      let (reraise, info) = CErrors.push reraise in
      let info = begin
        match Loc.get_loc info with
        | None   -> Option.cata (Loc.add_loc info) info loc
        | Some _ -> info
      end in iraise (reraise, info)

(* Load a vernac file. CErrors are annotated with file and location *)
and load_vernac ~verbosely ~check ~interactive doc sid file =
  let ft_beautify, close_beautify =
    if !Flags.beautify_file then
      let chan_beautify = open_out (file^beautify_suffix) in
      set_formatter_translator chan_beautify, fun () -> close_out chan_beautify;
    else
      !Topfmt.std_ft, fun () -> ()
  in
  let in_chan = open_utf8_file_in file in
  let in_echo = if verbosely then Some (open_utf8_file_in file) else None in
  let in_pa   = Pcoq.Gram.parsable ~file:(Loc.InFile file) (Stream.of_channel in_chan) in
  let rsid = ref sid in
  let rdoc = ref doc in
  try
    (* we go out of the following infinite loop when a End_of_input is
     * raised, which means that we raised the end of the file being loaded *)
    while true do
      let loc, ast =
          Stm.parse_sentence ~doc:!rdoc !rsid in_pa
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
      if !Flags.beautify then pr_new_syntax ?loc in_pa ft_beautify (Some ast);
      Option.iter (vernac_echo ?loc) in_echo;

      checknav_simple (loc, ast);
      let ndoc, nsid = Flags.silently (interp_vernac ~check ~interactive !rdoc !rsid) (loc, ast) in
      rsid := nsid;
      rdoc := ndoc
    done;
    !rdoc, !rsid
  with any ->   (* whatever the exception *)
    let (e, info) = CErrors.push any in
    close_in in_chan;
    Option.iter close_in in_echo;
    match e with
      | Stm.End_of_input ->
          (* Is this called so comments at EOF are printed? *)
          if !Flags.beautify then
            pr_new_syntax ~loc:(Loc.make_loc (max_int,max_int)) in_pa ft_beautify None;
          if !Flags.beautify_file then close_beautify ();
          !rdoc, !rsid
      | reraise ->
         if !Flags.beautify_file then close_beautify ();
	 iraise (disable_drop e, info)

(** [eval_expr : ?preserving:bool -> Loc.t * Vernacexpr.vernac_expr -> unit]
   It executes one vernacular command. By default the command is
   considered as non-state-preserving, in which case we add it to the
   Backtrack stack (triggering a save of a frozen state and the generation
   of a new state label). An example of state-preserving command is one coming
   from the query panel of Coqide. *)

let process_expr doc sid loc_ast =
  checknav_deep loc_ast;
  interp_vernac ~interactive:true ~check:true doc sid loc_ast
