(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Glob_term
open Topconstr

val declare_reserved_type : identifier located -> aconstr -> unit
val find_reserved_type : identifier -> aconstr
val anonymize_if_reserved : name -> glob_constr -> glob_constr
