(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr

(** Operations concerning records and canonical structures *)

(** {6 Records } *)
(** A structure S is a non recursive inductive type with a single
   constructor (the name of which defaults to Build_S) *)

type proj_kind = {
  pk_name: Name.t;
  pk_true_proj: bool;
  pk_canonical: bool;
}

type struc_typ = {
  s_CONST : constructor;
  s_EXPECTEDPARAM : int;
  s_PROJKIND : proj_kind list;
  s_PROJ : Constant.t option list }

type struc_tuple =
    constructor * proj_kind list * Constant.t option list

val register_structure : Environ.env -> struc_tuple -> unit
val subst_structure : Mod_subst.substitution -> struc_tuple -> struc_tuple

(** [lookup_structure isp] returns the struc_typ associated to the
   inductive path [isp] if it corresponds to a structure, otherwise
   it fails with [Not_found] *)
val lookup_structure : inductive -> struc_typ

(** [lookup_projections isp] returns the projections associated to the
   inductive path [isp] if it corresponds to a structure, otherwise
   it fails with [Not_found] *)
val lookup_projections : inductive -> Constant.t option list

(** raise [Not_found] if not a projection *)
val find_projection_nparams : GlobRef.t -> int

(** raise [Not_found] if not a projection *)
val find_projection : GlobRef.t -> struc_typ

val is_projection : Constant.t -> bool

(** Sets up the mapping from constants to primitive projections *)
val register_primitive_projection : Projection.Repr.t -> Constant.t -> unit

val is_primitive_projection : Constant.t -> bool

val find_primitive_projection : Constant.t -> Projection.Repr.t option

(** {6 Canonical structures } *)
(** A canonical structure declares "canonical" conversion hints between 
    the effective components of a structure and the projections of the  
    structure *)

(** A cs_pattern characterizes the form of a component of canonical structure *)
type cs_pattern =
    Const_cs of GlobRef.t
  | Prod_cs
  | Sort_cs of Sorts.family
  | Default_cs

type obj_typ = {
  o_DEF : constr;
  o_CTX : Univ.AUContext.t;
  o_INJ : int option;      (** position of trivial argument *)
  o_TABS : constr list;    (** ordered *)
  o_TPARAMS : constr list; (** ordered *)
  o_NPARAMS : int;
  o_TCOMPS : constr list } (** ordered *)

(** Return the form of the component of a canonical structure *)
val cs_pattern_of_constr : Environ.env -> constr -> cs_pattern * int option * constr list

val pr_cs_pattern : cs_pattern -> Pp.t

val lookup_canonical_conversion : (GlobRef.t * cs_pattern) -> constr * obj_typ
val register_canonical_structure : warn:bool -> Environ.env -> Evd.evar_map ->
  Constant.t * inductive -> unit
val subst_canonical_structure : Mod_subst.substitution -> Constant.t * inductive -> Constant.t * inductive
val is_open_canonical_projection :
  Environ.env -> Evd.evar_map -> Reductionops.state -> bool
val canonical_projections : unit ->
  ((GlobRef.t * cs_pattern) * obj_typ) list

val check_and_decompose_canonical_structure : Environ.env -> Evd.evar_map -> GlobRef.t -> Constant.t * inductive
