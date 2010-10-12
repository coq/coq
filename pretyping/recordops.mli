(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Nametab
open Term
open Libnames
open Libobject
open Library

(** Operations concerning records and canonical structures *)

(** {6 Records } *)
(** A structure S is a non recursive inductive type with a single
   constructor (the name of which defaults to Build_S) *)

type struc_typ = {
  s_CONST : constructor;
  s_EXPECTEDPARAM : int;
  s_PROJKIND : (name * bool) list;
  s_PROJ : constant option list }

val declare_structure :
  inductive * constructor * (name * bool) list * constant option list -> unit

(** [lookup_structure isp] returns the struc_typ associated to the
   inductive path [isp] if it corresponds to a structure, otherwise
   it fails with [Not_found] *)
val lookup_structure : inductive -> struc_typ

(** [lookup_projections isp] returns the projections associated to the
   inductive path [isp] if it corresponds to a structure, otherwise
   it fails with [Not_found] *)
val lookup_projections : inductive -> constant option list

(** raise [Not_found] if not a projection *)
val find_projection_nparams : global_reference -> int

(** raise [Not_found] if not a projection *)
val find_projection : global_reference -> struc_typ

(** we keep an index (dnet) of record's arguments + fields
   (=methods). Here is how to declare them: *)
val declare_method :
  global_reference -> Evd.evar -> Evd.evar_map -> unit
  (** and here is how to search for methods matched by a given term: *)
val methods_matching : constr ->
  ((global_reference*Evd.evar*Evd.evar_map) *
     (constr*existential_key)*Termops.subst) list

(** {6 Canonical structures } *)
(** A canonical structure declares "canonical" conversion hints between 
    the effective components of a structure and the projections of the  
    structure *)

type cs_pattern =
    Const_cs of global_reference
  | Prod_cs
  | Sort_cs of sorts_family
  | Default_cs

type obj_typ = {
  o_DEF : constr;
  o_INJ : int;      (** position of trivial argument *)
  o_TABS : constr list;    (** ordered *)
  o_TPARAMS : constr list; (** ordered *)
  o_NPARAMS : int;
  o_TCOMPS : constr list } (** ordered *)

val cs_pattern_of_constr : constr -> cs_pattern * int * constr list
val pr_cs_pattern : cs_pattern -> Pp.std_ppcmds

val lookup_canonical_conversion : (global_reference * cs_pattern) -> obj_typ
val declare_canonical_structure : global_reference -> unit
val is_open_canonical_projection :
  Evd.evar_map -> (constr * constr list) -> bool
val canonical_projections : unit ->
  ((global_reference * cs_pattern) * obj_typ) list
