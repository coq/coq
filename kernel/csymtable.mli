(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Names
open Constr
open Pre_env

val val_of_constr : env -> constr -> Vmvalues.values

val set_opaque_const      : Constant.t -> unit
val set_transparent_const : Constant.t -> unit
