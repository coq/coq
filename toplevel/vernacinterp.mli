(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Interpretation of extended vernac phrases. *)

val vinterp_add : Vernacexpr.extend_name -> (Genarg.raw_generic_argument list -> unit -> unit) -> unit
val overwriting_vinterp_add :
  Vernacexpr.extend_name -> (Genarg.raw_generic_argument list -> unit -> unit) -> unit

val vinterp_init : unit -> unit
val call : ?locality:bool -> Vernacexpr.extend_name * Genarg.raw_generic_argument list -> unit
