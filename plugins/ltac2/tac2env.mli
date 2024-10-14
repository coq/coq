(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
open Tac2val

(** Ltac2 global environment *)

(** {5 Toplevel definition of values} *)

type global_data = {
  gdata_expr : glb_tacexpr;
  gdata_type : type_scheme;
  gdata_mutable : bool;
  gdata_deprecation : Deprecation.t option;
}

val define_global : ltac_constant -> global_data -> unit
val interp_global : ltac_constant -> global_data

type compile_info = {
  source : string;
}

val set_compiled_global : ltac_constant -> compile_info -> valexpr -> unit
val get_compiled_global : ltac_constant -> (compile_info * valexpr) option

val globals : unit -> global_data KNmap.t

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

val define_constructor : ?warn:UserWarn.t -> ltac_constructor -> constructor_data -> unit
val interp_constructor : ltac_constructor -> constructor_data

val find_all_constructors_in_type : type_constant -> constructor_data KNmap.t
(** Useful for printing info about currently defined constructors of open types. *)

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

type alias_data = {
  alias_body : raw_tacexpr;
  alias_depr : Deprecation.t option;
}

val define_alias : ?deprecation:Deprecation.t -> ltac_constant -> raw_tacexpr -> unit
val interp_alias : ltac_constant -> alias_data

(** {5 Toplevel definition of notations} *)

(* no deprecation info: deprecation warning is emitted by the parser *)
type notation_data =
  | UntypedNota of raw_tacexpr
  | TypedNota of {
      nota_prms : int;
      nota_argtys : int glb_typexpr Id.Map.t;
      nota_ty : int glb_typexpr;
      nota_body : glb_tacexpr;
    }

val define_notation : ltac_notation -> notation_data -> unit
val interp_notation : ltac_notation -> notation_data

(** {5 Name management} *)

val push_ltac : visibility -> full_path -> tacref -> unit
val locate_ltac : qualid -> tacref
val locate_extended_all_ltac : qualid -> tacref list
val shortest_qualid_of_ltac : Id.Set.t -> tacref -> qualid
val path_of_ltac : tacref -> full_path

val push_constructor : visibility -> full_path -> ltac_constructor -> unit
val locate_constructor : qualid -> ltac_constructor
val locate_extended_all_constructor : qualid -> ltac_constructor list
val shortest_qualid_of_constructor : ltac_constructor -> qualid
val path_of_constructor : ltac_constructor -> full_path

(** Emit warning if any for the constructor. *)
val constructor_user_warn : ?loc:Loc.t -> ltac_constructor -> unit

val push_type : visibility -> full_path -> type_constant -> unit
val locate_type : qualid -> type_constant
val locate_extended_all_type : qualid -> type_constant list
val shortest_qualid_of_type : ?loc:Loc.t -> type_constant -> qualid
val path_of_type : type_constant -> full_path

val push_projection : visibility -> full_path -> ltac_projection -> unit
val locate_projection : qualid -> ltac_projection
val locate_extended_all_projection : qualid -> ltac_projection list
val shortest_qualid_of_projection : ltac_projection -> qualid

(** {5 Toplevel definitions of ML tactics} *)

(** This state is not part of the summary, contrarily to the ones above. It is
    intended to be used from ML plugins to register ML-side functions. *)

val define_primitive : ml_tactic_name -> valexpr -> unit
val interp_primitive : ml_tactic_name -> valexpr

(** {5 ML primitive types} *)

type 'a or_glb_tacexpr =
| GlbVal of 'a
| GlbTacexpr of glb_tacexpr

type ('a, 'b, 'r) intern_fun = Genintern.glob_sign -> 'a -> 'b * 'r glb_typexpr

type environment = {
  env_ist : valexpr Id.Map.t;
}

type ('a, 'b) ml_object = {
  ml_intern : 'r. ('a, 'b or_glb_tacexpr, 'r) intern_fun;
  ml_subst : Mod_subst.substitution -> 'b -> 'b;
  ml_interp : environment -> 'b -> valexpr Proofview.tactic;
  ml_print : Environ.env -> Evd.evar_map -> 'b -> Pp.t;
  ml_raw_print : Environ.env -> Evd.evar_map -> 'a -> Pp.t;
}

val define_ml_object : ('a, 'b) Tac2dyn.Arg.tag -> ('a, 'b) ml_object -> unit
val interp_ml_object : ('a, 'b) Tac2dyn.Arg.tag -> ('a, 'b) ml_object

(** {5 Absolute paths} *)

val rocq_prefix : ModPath.t
(** Path where primitive datatypes are defined in Ltac2 plugin. *)

val coq_prefix : ModPath.t [@@ocaml.deprecated "(9.0) Use rocq_prefix"]
(** Path where primitive datatypes are defined in Ltac2 plugin. *)

val std_prefix : ModPath.t
(** Path where Ltac-specific datatypes are defined in Ltac2 plugin. *)

val ltac1_prefix : ModPath.t
(** Path where the Ltac1 legacy FFI is defined. *)

(** {5 Generic arguments} *)

val wit_ltac2_constr : (raw_tacexpr, Id.Set.t * glb_tacexpr, Util.Empty.t) genarg_type
(** Ltac2 quotations in Gallina terms *)

type var_quotation_kind =
  | ConstrVar
  | PretermVar
  | PatternVar

val wit_ltac2_var_quotation : (lident option * lident, var_quotation_kind * Id.t, Util.Empty.t) genarg_type
(** Ltac2 quotations for variables "$x" or "$kind:foo" in Gallina terms.
    NB: "$x" means "$constr:x" *)

(** {5 Helper functions} *)

val is_constructor_id : Id.t -> bool
val is_constructor : qualid -> bool
