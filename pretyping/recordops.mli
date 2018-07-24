(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
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

type struc_typ = {
  s_CONST : constructor;
  s_EXPECTEDPARAM : int;
  s_PROJKIND : (Name.t * bool) list;
  s_PROJ : Constant.t option list }

type struc_tuple =
    inductive * constructor * (Name.t * bool) list * Constant.t option list

val declare_structure : struc_tuple -> unit

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

(** Sets up the mapping from constants to primitive projections *)
val declare_primitive_projection : Projection.Repr.t -> unit

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
val declare_canonical_structure : GlobRef.t -> unit
val is_open_canonical_projection :
  Environ.env -> Evd.evar_map -> Reductionops.state -> bool
val canonical_projections : unit ->
  ((GlobRef.t * cs_pattern) * obj_typ) list
