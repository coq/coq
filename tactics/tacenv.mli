(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Tacexpr

(** This module centralizes the various ways of registering tactics. *)

type alias = KerName.t
(** Type of tactic alias, used in the [TacAlias] node. *)

val register_alias : alias -> DirPath.t -> glob_tactic_expr -> unit
(** Register a tactic alias. *)

val interp_alias : alias -> (DirPath.t * glob_tactic_expr)
(** Recover the the body of an alias. *)
