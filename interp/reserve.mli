(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Pp
open Names
open Glob_term
open Notation_term

val declare_reserved_type : identifier located list -> notation_constr -> unit
val find_reserved_type : identifier -> notation_constr
val anonymize_if_reserved : name -> glob_constr -> glob_constr
