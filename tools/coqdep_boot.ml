(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

let rec parse = function
  | "-natdynlink" :: "no" :: ll -> option_natdynlk := false; parse ll
  | "-c" :: ll -> option_c := true; parse ll
  | "-boot" :: ll -> parse ll (* We're already in boot mode by default *)
  | "-mldep" :: ocamldep :: ll ->
      option_mldep := Some ocamldep; option_c := true; parse ll
  | "-I" :: r :: ll ->
       (* To solve conflict (e.g. same filename in kernel and checker)
          we allow to state an explicit order *)
       add_caml_dir r;
       norec_dirs:=r::!norec_dirs;
       parse ll
  | f :: ll -> treat_file None f; parse ll
  | [] -> ()

let coqdep_boot () =
  let () = option_boot := true in
  if Array.length Sys.argv < 2 then exit 1;
  parse (List.tl (Array.to_list Sys.argv));
  if !option_c then begin
    add_rec_dir add_known "." [];
    add_rec_dir (fun _ -> add_caml_known) "." ["Coq"];
  end
  else begin
    add_rec_dir add_known "theories" ["Coq"];
    add_rec_dir add_known "plugins" ["Coq"];
    add_caml_dir "tactics";
    add_rec_dir (fun _ -> add_caml_known) "theories" ["Coq"];
    add_rec_dir (fun _ -> add_caml_known) "plugins" ["Coq"];
  end;
  if !option_c then mL_dependencies ();
  coq_dependencies ()

let _ = Printexc.catch coqdep_boot ()
