(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Misctypes
open Tac2qexpr
open Tac2expr

(** Syntactic quoting of expressions. *)

(** Contrarily to Tac2ffi, which lives on the semantic level, this module
    manipulates pure syntax of Ltac2. Its main purpose is to write notations. *)

val constructor : ?loc:Loc.t -> ltac_constructor -> raw_tacexpr list -> raw_tacexpr

val of_anti : ?loc:Loc.t -> (?loc:Loc.t -> 'a -> raw_tacexpr) -> 'a or_anti -> raw_tacexpr

val of_int : ?loc:Loc.t -> int -> raw_tacexpr

val of_pair : ?loc:Loc.t -> raw_tacexpr * raw_tacexpr -> raw_tacexpr

val of_variable : ?loc:Loc.t -> Id.t -> raw_tacexpr

val of_ident : ?loc:Loc.t -> Id.t -> raw_tacexpr

val of_constr : ?loc:Loc.t -> Constrexpr.constr_expr -> raw_tacexpr

val of_open_constr : ?loc:Loc.t -> Constrexpr.constr_expr -> raw_tacexpr

val of_list : ?loc:Loc.t -> raw_tacexpr list -> raw_tacexpr

val of_bindings : ?loc:Loc.t -> bindings -> raw_tacexpr

val of_intro_pattern : ?loc:Loc.t -> intro_pattern -> raw_tacexpr

val of_intro_patterns : ?loc:Loc.t -> intro_pattern list -> raw_tacexpr
