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
    are [Coqdep_lexer] and [Unix], and it should stay so.
    If it need someday some additional information, pass it via
    options (see for instance [option_natdynlk] below).
*)

let rec parse = function
  | "-slash" :: ll -> option_slash := true; parse ll
  | "-natdynlink" :: "no" :: ll -> option_natdynlk := false; parse ll
  | "-c" :: ll -> option_c := true; parse ll
  | "-boot" :: ll -> parse ll (* We're already in boot mode by default *)
  | f :: ll -> treat_file None f; parse ll
  | [] -> ()

let coqdep_boot () =
  if Array.length Sys.argv < 2 then exit 1;
  parse (List.tl (Array.to_list Sys.argv));
  add_rec_dir add_known "theories" ["Coq"];
  add_rec_dir add_known "contrib" ["Coq"];
  List.iter (fun (f,d) -> add_mli_known f d) !mliAccu;
  List.iter (fun (f,d) -> add_mllib_known f d) !mllibAccu;
  List.iter (fun (f,_,d) -> add_ml_known f d) !mlAccu;
  warning_mult ".mli" iter_mli_known;
  warning_mult ".ml" iter_ml_known;
  if !option_c then mL_dependencies ();
  coq_dependencies ()

let _ = Printexc.catch coqdep_boot ()
