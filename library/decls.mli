(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Names
open Sign
open Libnames
open Decl_kinds

(** This module manages non-kernel informations about declarations. It
    is either non-logical informations or logical informations that
    have no place to be (yet) in the kernel *)

(** Registration and access to the table of variable *)

type variable_data =
    dir_path * bool (* opacity *) * Univ.constraints * logical_kind

val add_variable_data : variable -> variable_data -> unit
val variable_path : variable -> dir_path
val variable_secpath : variable -> qualid
val variable_kind : variable -> logical_kind
val variable_opacity : variable -> bool
val variable_constraints : variable -> Univ.constraints
val variable_exists : variable -> bool

(** Registration and access to the table of constants *)

val add_constant_kind : constant -> logical_kind -> unit
val constant_kind : constant -> logical_kind

(** Miscellaneous functions *)

val last_section_hyps : dir_path -> identifier list
val clear_proofs : named_context -> Environ.named_context_val
