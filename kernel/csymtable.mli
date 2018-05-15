(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* $Id$ *)

open Names
open Constr
open Environ

val val_of_constr : env -> constr -> Vmvalues.values

val set_opaque_const      : Constant.t -> unit
val set_transparent_const : Constant.t -> unit

val get_global_data : unit -> Vmvalues.vm_global
