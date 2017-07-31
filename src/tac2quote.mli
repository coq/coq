(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Misctypes
open Tac2expr

(** Syntactic quoting of expressions. *)

(** Contrarily to Tac2ffi, which lives on the semantic level, this module
    manipulates pure syntax of Ltac2. Its main purpose is to write notations. *)

val constructor : ?loc:Loc.t -> ltac_constructor -> raw_tacexpr list -> raw_tacexpr

val of_int : ?loc:Loc.t -> int -> raw_tacexpr

val of_pair : ?loc:Loc.t -> raw_tacexpr * raw_tacexpr -> raw_tacexpr

val of_variable : ?loc:Loc.t -> Id.t -> raw_tacexpr

val of_ident : ?loc:Loc.t -> Id.t -> raw_tacexpr

val of_constr : ?loc:Loc.t -> Constrexpr.constr_expr -> raw_tacexpr

val of_list : ?loc:Loc.t -> raw_tacexpr list -> raw_tacexpr

val of_bindings : ?loc:Loc.t -> raw_tacexpr bindings -> raw_tacexpr
