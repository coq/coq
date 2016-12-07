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

(** {5 Toplevel definition of values} *)

val define_global : ltac_constant -> (glb_tacexpr * type_scheme) -> unit
val interp_global : ltac_constant -> (valexpr * type_scheme)

(** {5 Toplevel definition of types} *)

val define_type : type_constant -> glb_quant_typedef -> unit
val interp_type : type_constant -> glb_quant_typedef

(** {5 Toplevel definition of algebraic constructors} *)

type constructor_data = {
  cdata_prms : int;
  (** Type parameters *)
  cdata_type : type_constant;
  (** Inductive definition to which the constructor pertains *)
  cdata_args : int glb_typexpr list;
  (** Types of the constructor arguments *)
  cdata_indx : int;
  (** Index of the constructor in the ADT. Numbering is duplicated between
      argumentless and argument-using constructors, e.g. in type ['a option]
      [None] and [Some] have both index 0. *)
}

val define_constructor : ltac_constructor -> constructor_data -> unit
val interp_constructor : ltac_constructor -> constructor_data

(** {5 Toplevel definition of projections} *)

type projection_data = {
  pdata_prms : int;
  (** Type parameters *)
  pdata_type : type_constant;
  (** Record definition to which the projection pertains *)
  pdata_ptyp : int glb_typexpr;
  (** Type of the projection *)
  pdata_mutb : bool;
  (** Whether the field is mutable *)
  pdata_indx : int;
  (** Index of the projection *)
}

val define_projection : ltac_projection -> projection_data -> unit
val interp_projection : ltac_projection -> projection_data

(** {5 Name management} *)

type tacref =
| TacConstant of ltac_constant
| TacConstructor of ltac_constructor

val push_ltac : visibility -> full_path -> tacref -> unit
val locate_ltac : qualid -> tacref
val locate_extended_all_ltac : qualid -> tacref list

val push_type : visibility -> full_path -> type_constant -> unit
val locate_type : qualid -> type_constant
val locate_extended_all_type : qualid -> type_constant list

val push_projection : visibility -> full_path -> ltac_projection -> unit
val locate_projection : qualid -> ltac_projection
val locate_extended_all_projection : qualid -> ltac_projection list

(** {5 Toplevel definitions of ML tactics} *)

(** This state is not part of the summary, contrarily to the ones above. It is
    intended to be used from ML plugins to register ML-side functions. *)

val define_primitive : ml_tactic_name -> ml_tactic -> unit
val interp_primitive : ml_tactic_name -> ml_tactic

(** {5 ML primitive types} *)

type 'a ml_object = {
  ml_type : type_constant;
  ml_interp : environment -> 'a -> Geninterp.Val.t Proofview.tactic;
}

val define_ml_object : ('a, 'b, 'c) genarg_type -> 'b ml_object -> unit
val interp_ml_object : ('a, 'b, 'c) genarg_type -> 'b ml_object

(** {5 Absolute paths} *)

val coq_prefix : ModPath.t
(** Path where primitive datatypes are defined in Ltac2 plugin. *)

(** {5 Generic arguments} *)

val wit_ltac2 : (raw_tacexpr, glb_tacexpr, Util.Empty.t) genarg_type
