(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Genarg
open Names
open Libnames
open Nametab
open Tac2expr
open Tac2ffi

(** Ltac2 global environment *)

(** {5 Toplevel definition of values} *)

type global_data = {
  gdata_expr : glb_tacexpr;
  gdata_type : type_scheme;
  gdata_mutable : bool;
}

val define_global : ltac_constant -> global_data -> unit
val interp_global : ltac_constant -> global_data

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
  cdata_indx : int option;
  (** Index of the constructor in the ADT. Numbering is duplicated between
      argumentless and argument-using constructors, e.g. in type ['a option]
      [None] and [Some] have both index 0. This field is empty whenever the
      constructor is a member of an open type. *)
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

(** {5 Toplevel definition of aliases} *)

val define_alias : ltac_constant -> raw_tacexpr -> unit
val interp_alias : ltac_constant -> raw_tacexpr

(** {5 Name management} *)

val push_ltac : visibility -> full_path -> tacref -> unit
val locate_ltac : qualid -> tacref
val locate_extended_all_ltac : qualid -> tacref list
val shortest_qualid_of_ltac : tacref -> qualid

val push_constructor : visibility -> full_path -> ltac_constructor -> unit
val locate_constructor : qualid -> ltac_constructor
val locate_extended_all_constructor : qualid -> ltac_constructor list
val shortest_qualid_of_constructor : ltac_constructor -> qualid

val push_type : visibility -> full_path -> type_constant -> unit
val locate_type : qualid -> type_constant
val locate_extended_all_type : qualid -> type_constant list
val shortest_qualid_of_type : ?loc:Loc.t -> type_constant -> qualid

val push_projection : visibility -> full_path -> ltac_projection -> unit
val locate_projection : qualid -> ltac_projection
val locate_extended_all_projection : qualid -> ltac_projection list
val shortest_qualid_of_projection : ltac_projection -> qualid

(** {5 Toplevel definitions of ML tactics} *)

(** This state is not part of the summary, contrarily to the ones above. It is
    intended to be used from ML plugins to register ML-side functions. *)

val define_primitive : ml_tactic_name -> closure -> unit
val interp_primitive : ml_tactic_name -> closure

(** {5 ML primitive types} *)

type 'a or_glb_tacexpr =
| GlbVal of 'a
| GlbTacexpr of glb_tacexpr

type ('a, 'b, 'r) intern_fun = Genintern.glob_sign -> 'a -> 'b * 'r glb_typexpr

type environment = {
  env_ist : valexpr Id.Map.t;
}

type ('a, 'b) ml_object = {
  ml_intern : 'r. (raw_tacexpr, glb_tacexpr, 'r) intern_fun -> ('a, 'b or_glb_tacexpr, 'r) intern_fun;
  ml_subst : Mod_subst.substitution -> 'b -> 'b;
  ml_interp : environment -> 'b -> valexpr Proofview.tactic;
  ml_print : Environ.env -> 'b -> Pp.t;
}

val define_ml_object : ('a, 'b) Tac2dyn.Arg.tag -> ('a, 'b) ml_object -> unit
val interp_ml_object : ('a, 'b) Tac2dyn.Arg.tag -> ('a, 'b) ml_object

(** {5 Absolute paths} *)

val coq_prefix : ModPath.t
(** Path where primitive datatypes are defined in Ltac2 plugin. *)

val std_prefix : ModPath.t
(** Path where Ltac-specific datatypes are defined in Ltac2 plugin. *)

val ltac1_prefix : ModPath.t
(** Path where the Ltac1 legacy FFI is defined. *)

(** {5 Generic arguments} *)

val wit_ltac2 : (raw_tacexpr, glb_tacexpr, Util.Empty.t) genarg_type
val wit_ltac2_quotation : (Id.t Loc.located, Id.t, Util.Empty.t) genarg_type

(** {5 Helper functions} *)

val is_constructor : qualid -> bool
