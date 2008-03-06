(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: classes.mli 6748 2005-02-18 22:17:50Z herbelin $ i*)

(*i*)
open Names
open Libnames
open Decl_kinds
open Term
open Sign
open Evd
open Environ
open Nametab
open Mod_subst
open Topconstr
open Util
(*i*)

(* This module defines type-classes *)
type typeclass = {
  (* Name of the class. FIXME: should not necessarily be globally unique. *)
  cl_name : identifier;

  (* Context in which the definitions are typed. Includes both typeclass parameters and superclasses. The boolean indicates if the 
     typeclass argument is a direct superclass. *)
  cl_context : ((identifier * bool) option * named_declaration) list; 

  cl_params : int; (* This is the length of the suffix of the context which should be considered explicit parameters. *)

  (* Context of definitions and properties on defs, will not be shared *)
  cl_props : named_context;

  (* The class implementation: a record parameterized by the context with defs in it. *)
  cl_impl : inductive; 
}

type instance = {
  is_class: typeclass;
  is_pri : int option;
  is_impl: constant;
}
  
val instances : Libnames.reference -> instance list
val typeclasses : unit -> typeclass list
val add_class : typeclass -> unit
val add_instance : instance -> unit

val register_add_instance_hint : (reference -> int option -> unit) -> unit
val add_instance_hint : reference -> int option -> unit

val class_info : identifier -> typeclass (* raises Not_found *)
val class_of_inductive : inductive -> typeclass (* raises Not_found *)

val resolve_one_typeclass : env -> types -> types (* Raises Not_found *)
val resolve_one_typeclass_evd : env -> evar_defs ref -> types -> types (* Raises Not_found *)

val is_class : inductive -> bool

val class_of_constr : constr -> typeclass option

val resolve_typeclass : env -> evar -> evar_info -> evar_defs * bool -> evar_defs * bool
val resolve_typeclasses : ?onlyargs:bool -> ?all:bool -> env -> evar_map -> evar_defs -> evar_defs

val solve_instanciation_problem : (env -> evar_defs -> existential_key -> evar_info -> evar_defs * bool) ref
val solve_instanciations_problem : (env -> evar_defs -> bool -> bool -> evar_defs) ref

type substitution = (identifier * constr) list

val substitution_of_named_context : 
  evar_defs ref -> env -> identifier -> int ->
  substitution -> named_context -> substitution

val nf_substitution : evar_map -> substitution -> substitution

val is_implicit_arg : hole_kind -> bool


val subst :  'a * Mod_subst.substitution *
    ((Names.identifier, typeclass) Gmap.t * 'b * ('c, instance list) Gmap.t) ->
    (Names.identifier, typeclass) Gmap.t * 'b * ('c, instance list) Gmap.t

val qualid_of_con : Names.constant -> Libnames.reference
