(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Versions of declare with support for interpretation heurisitics *)

open Names
open Libnames
open Entries

val declare_variable : variable -> Declare.variable_declaration -> object_name

val declare_constant :
 ?internal:Declare.internal_flag -> ?local:bool -> Id.t -> ?export_seff:bool -> Declare.constant_declaration -> constant

val declare_mind : mutual_inductive_entry -> object_name * bool
