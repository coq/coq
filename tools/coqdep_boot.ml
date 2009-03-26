(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Coqdep_common

(** [coqdep_boot] is a stripped-down version of [coqdep], whose
    behavior is the one of [coqdep -boot]. Its only dependencies
    are [Coqdep_lexer], [Coqdep_common] and [Unix], and it should stay so.
    If it needs someday some additional information, pass it via
    options (see for instance [option_natdynlk] below).
*)

let rec parse = function
  | "-slash" :: ll -> option_slash := true; parse ll
  | "-natdynlink" :: "no" :: ll -> option_natdynlk := false; parse ll
  | "-c" :: ll -> option_c := true; parse ll
  | "-boot" :: ll -> parse ll (* We're already in boot mode by default *)
  | "-I" :: r :: ll ->
       (* To solve conflict (e.g. same filename in kernel and checker)
          we allow to state an explicit order *)
       add_dir add_known r [];
       norecdir_list:=r::!norecdir_list;
       parse ll
  | f :: ll -> treat_file None f; parse ll
  | [] -> ()

let coqdep_boot () =
  if Array.length Sys.argv < 2 then exit 1;
  parse (List.tl (Array.to_list Sys.argv));
  if !option_c then
    add_rec_dir add_known "." []
  else begin
    add_rec_dir add_known "theories" ["Coq"];
    add_rec_dir add_known "plugins" ["Coq"];
  end;
  if !option_c then mL_dependencies ();
  coq_dependencies ()

let _ = Printexc.catch coqdep_boot ()
