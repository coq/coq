(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Notation_term

(** Syntactic definitions. *)

type syndef_interpretation = (Id.t * subscopes) list * notation_constr

val declare_syntactic_definition : bool -> Id.t ->
  Flags.compat_version option -> syndef_interpretation -> unit

val search_syntactic_definition : kernel_name -> syndef_interpretation

(** Options concerning verbose display of compatibility notations
    or their deactivation *)

val set_verbose_compat_notations : bool -> unit
val set_compat_notations : bool -> unit
