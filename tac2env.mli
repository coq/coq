(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Genarg
open Names
open Libnames
open Nametab
open Tac2expr

(** Ltac2 global environment *)

type ltac_constant = KerName.t
type ltac_constructor = KerName.t
type type_constant = KerName.t

(** {5 Toplevel definition of values} *)

val define_global : ltac_constant -> (glb_tacexpr * type_scheme) -> unit
val interp_global : ltac_constant -> (valexpr * type_scheme)

(** {5 Toplevel definition of types} *)

val define_type : type_constant -> glb_quant_typedef -> unit
val interp_type : type_constant -> glb_quant_typedef

(** {5 Toplevel definition of algebraic constructors} *)

type constructor_data = {
  cdata_type : type_constant;
  cdata_args : int * int glb_typexpr list;
  cdata_indx : int;
}

val define_constructor : ltac_constructor -> constructor_data -> unit
val interp_constructor : ltac_constructor -> constructor_data

(** {5 Name management} *)

val push_ltac : visibility -> full_path -> ltac_constant -> unit
val locate_ltac : qualid -> ltac_constant
val locate_extended_all_ltac : qualid -> ltac_constant list

val push_type : visibility -> full_path -> type_constant -> unit
val locate_type : qualid -> type_constant
val locate_extended_all_type : qualid -> type_constant list

(** {5 Toplevel definitions of ML tactics} *)

(** This state is not part of the summary, contrarily to the ones above. It is
    intended to be used from ML plugins to register ML-side functions. *)

val define_primitive : ml_tactic_name -> ml_tactic -> unit
val interp_primitive : ml_tactic_name -> ml_tactic
