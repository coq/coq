(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Coqdep_common

(** [coqdep_boot] is a stripped-down version of [coqdep], whose
    behavior is the one of [coqdep -boot]. Its only dependencies
    are [Coqdep_lexer], [Coqdep_common] and [Unix], and it should stay so.
    If it needs someday some additional information, pass it via
    options (see for instance [option_natdynlk] below).
*)

let split_period = Str.split (Str.regexp (Str.quote "."))
let add_q_include path l = add_rec_dir_no_import add_known path (split_period l)
let add_r_include path l = add_rec_dir_import add_known path (split_period l)

let rec parse = function
  | "-dyndep" :: "no" :: ll -> option_dynlink := No; parse ll
  | "-dyndep" :: "opt" :: ll -> option_dynlink := Opt; parse ll
  | "-dyndep" :: "byte" :: ll -> option_dynlink := Byte; parse ll
  | "-dyndep" :: "both" :: ll -> option_dynlink := Both; parse ll
  | "-dyndep" :: "var" :: ll -> option_dynlink := Variable; parse ll
  | "-boot" :: ll -> parse ll (* We're already in boot mode by default *)
  | "-I" :: r :: ll ->
       (* To solve conflict (e.g. same filename in kernel and checker)
          we allow to state an explicit order *)
       add_caml_dir r;
       norec_dirs := StrSet.add r !norec_dirs;
       parse ll
  | "-R" :: r :: ln :: ll -> add_r_include r ln; parse ll
  | "-Q" :: r :: ln :: ll -> add_q_include r ln; parse ll
  | f :: ll -> treat_file None f; parse ll
  | [] -> ()

let _ =
  let () = option_boot := true in
  if Array.length Sys.argv < 2 then exit 1;
  parse (List.tl (Array.to_list Sys.argv));
  coq_dependencies ()
