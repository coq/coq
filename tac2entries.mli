(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Names
open Libnames
open Tac2expr

(** {5 Toplevel definitions} *)

val register_ltac : ?local:bool -> rec_flag ->
  (Name.t located * raw_tacexpr) list -> unit

val register_type : ?local:bool -> rec_flag ->
  (qualid located * redef_flag * raw_quant_typedef) list -> unit

val register_primitive : ?local:bool ->
  Id.t located -> raw_typexpr -> ml_tactic_name -> unit

val register_struct : ?local:bool -> strexpr -> unit

(** {5 Inspecting} *)

val print_ltac : Libnames.reference -> unit

(** {5 Eval loop} *)

(** Evaluate a tactic expression in the current environment *)
val call : default:bool -> raw_tacexpr -> unit
