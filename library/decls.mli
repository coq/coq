(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Libnames
open Decl_kinds

(** This module manages non-kernel informations about declarations. It
    is either non-logical informations or logical informations that
    have no place to be (yet) in the kernel *)

(** Registration and access to the table of variable *)

type variable_data = {
  path:DirPath.t;
  opaque:bool;
  univs:Univ.ContextSet.t;
  poly:bool;
  kind:logical_kind;
}

val add_variable_data : variable -> variable_data -> unit
val variable_path : variable -> DirPath.t
val variable_secpath : variable -> qualid
val variable_kind : variable -> logical_kind
val variable_opacity : variable -> bool
val variable_context : variable -> Univ.ContextSet.t
val variable_polymorphic : variable -> bool
val variable_exists : variable -> bool

(** Registration and access to the table of constants *)

val add_constant_kind : Constant.t -> logical_kind -> unit
val constant_kind : Constant.t -> logical_kind
