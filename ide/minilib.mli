(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** Some excerpts of Util and similar files to avoid depending on them
    and hence on Compat and Camlp4 *)

(** debug printing *)
val debug : bool ref
val prerr_endline : string -> unit

(** safe version of Pervasives.prerr_endline
    (avoid exception in win32 without console) *)
val safe_prerr_endline : string -> unit
