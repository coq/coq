(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp

let fatal_error msg =
  Topfmt.std_logger Feedback.Error msg;
  flush_all ();
  exit 1

let warn_file_no_extension =
  CWarnings.create ~name:"file-no-extension" ~category:CWarnings.CoreCategories.filesystem
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

let safe_chop_extension f =
  try Filename.chop_extension f with Invalid_argument _ -> f

let ensure_bname src tgt =
  let src, tgt = Filename.basename src, Filename.basename tgt in
  let src, tgt = safe_chop_extension src, safe_chop_extension tgt in
  if src <> tgt then
    fatal_error (str "Source and target file names must coincide, directories can differ" ++ fnl () ++
                   str "Source: " ++ str src                                                ++ fnl () ++
                   str "Target: " ++ str tgt)

let ensure ~ext ~src ~tgt = ensure_bname src tgt; ensure_ext ext tgt

let ensure_exists f =
  if not (Sys.file_exists f) then
    fatal_error (hov 0 (str "Can't find file" ++ spc () ++ str f))

let ensure_exists_with_prefix ~src ~tgt:f_out ~src_ext ~tgt_ext =
  let long_f_dot_src = ensure ~ext:src_ext ~src ~tgt:src in
  ensure_exists long_f_dot_src;
  let long_f_dot_tgt = match f_out with
    | None -> safe_chop_extension long_f_dot_src ^ tgt_ext
    | Some f -> ensure ~ext:tgt_ext ~src:long_f_dot_src ~tgt:f in
  long_f_dot_src, long_f_dot_tgt

let ensure_no_pending_proofs ~filename s =
  match s.Vernacstate.interp.lemmas with
  | Some lemmas ->
      let pfs = Vernacstate.LemmaStack.get_all_proof_names lemmas in
      fatal_error (str "There are pending proofs in file " ++ str filename ++ str": "
                    ++ (pfs
                        |> List.rev
                        |> prlist_with_sep pr_comma Names.Id.print)
                    ++ str ".");
  | None ->
    let pm = s.Vernacstate.interp.program in
    let what_for = Pp.str ("file " ^ filename) in
    NeList.iter (fun pm -> Declare.Obls.check_solved_obligations ~what_for ~pm) pm
