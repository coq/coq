(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Coqdep_common

(** [coqdep_boot] is a stripped-down version of [coqdep], whose
    behavior is the one of [coqdep -boot]. Its only dependencies
    are [Coqdep_lexer], [Coqdep_common] and [Unix], and it should stay so.
    If it needs someday some additional information, pass it via
    options (see for instance [option_natdynlk] below).
*)

(** when true, .v files will generate .v.d output *)
let file_output = ref false
  
let rec parse = function
  | "-dyndep" :: "no" :: ll -> option_dynlink := No; parse ll
  | "-dyndep" :: "opt" :: ll -> option_dynlink := Opt; parse ll
  | "-dyndep" :: "byte" :: ll -> option_dynlink := Byte; parse ll
  | "-dyndep" :: "both" :: ll -> option_dynlink := Both; parse ll
  | "-dyndep" :: "var" :: ll -> option_dynlink := Variable; parse ll
  | "-c" :: ll -> option_c := true; parse ll
  | "-boot" :: ll -> parse ll (* We're already in boot mode by default *)
  | "-mldep" :: ocamldep :: ll ->
      option_mldep := Some ocamldep; option_c := true; parse ll
  | "-I" :: r :: ll ->
       (* To solve conflict (e.g. same filename in kernel and checker)
          we allow to state an explicit order *)
       add_caml_dir r;
       norec_dirs := StrSet.add r !norec_dirs;
       parse ll
  | "-with-file-output" :: ll -> file_output := true; parse ll
  | f :: ll -> treat_file None f; parse ll
  | [] -> ()

let _ =
  let () = option_boot := true in
  if Array.length Sys.argv < 2 then exit 1;
  parse (List.tl (Array.to_list Sys.argv));
  if !option_c then begin
    add_rec_dir_import add_known "." [];
    add_rec_dir_import (fun _ -> add_caml_known) "." ["Coq"];
  end
  else begin
    add_rec_dir_import add_known "theories" ["Coq"];
    add_rec_dir_import add_known "plugins" ["Coq"];
    add_caml_dir "tactics";
    add_rec_dir_import (fun _ -> add_caml_known) "theories" ["Coq"];
    add_rec_dir_import (fun _ -> add_caml_known) "plugins" ["Coq"];
  end;
  if !option_c then mL_dependencies ();
  coq_dependencies !file_output
