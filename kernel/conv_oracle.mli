(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Names
open Closure

(* Order on section paths for unfolding.
   If oracle_order sp1 sp2 is true, then unfold sp1 first.
   Note: the oracle does not introduce incompleteness, it only
   tries to postpone unfolding of "opaque" constants. *)
val oracle_order : table_key -> table_key -> bool

(* Changing the oracle *)
val set_opaque_const      : section_path -> unit
val set_transparent_const : section_path -> unit

val set_opaque_var      : identifier -> unit
val set_transparent_var : identifier -> unit

(*****************************)

(* transparent state summary operations *)
val init     : unit -> unit
val freeze   : unit -> transparent_state
val unfreeze : transparent_state -> unit
