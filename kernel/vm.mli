(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Vmvalues

(** Debug printing *)

val set_drawinstr : unit -> unit

val reduce_fix : int -> vfix -> vfun array * values array
                              (** bodies ,  types *)

val reduce_cofix : int -> vcofix -> values array * values array
                                      (** bodies , types *)

val type_of_switch : vswitch -> values

val branch_of_switch : int -> vswitch -> (int * values) array

val reduce_fun : int -> vfun -> values

(** [decompose_vfun2 k f1 f2] takes two functions [f1] and [f2] at current
    DeBruijn level [k], with [n] lambdas in common, returns [n] and the reduced
    bodies under those lambdas. *)
val decompose_vfun2  : int -> vfun -> vfun -> int * values * values

(** Apply a value *)

val apply_whd : int -> whd -> values
