(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Names


(* Order on section paths for unfolding.
   If [oracle_order kn1 kn2] is true, then unfold kn1 first.
   Note: the oracle does not introduce incompleteness, it only
   tries to postpone unfolding of "opaque" constants. *)
val oracle_order : 'a tableKey -> 'a tableKey -> bool

(* Changing the oracle *)
val set_opaque_const      : constant -> unit
val set_transparent_const : constant -> unit

val set_opaque_var      : identifier -> unit
val set_transparent_var : identifier -> unit

val is_opaque_cst : constant -> bool
val is_opaque_var : identifier -> bool

(*****************************)

(* transparent state summary operations *)
val init     : unit -> unit
val freeze   : unit -> transparent_state
val unfreeze : transparent_state -> unit
