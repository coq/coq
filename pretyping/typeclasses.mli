(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

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
  (* The class implementation: a record parameterized by the context with defs in it or a definition if 
     the class is a singleton. This acts as the classe's global identifier. *)
  cl_impl : global_reference; 

  (* Context in which the definitions are typed. Includes both typeclass parameters and superclasses. 
     The boolean indicates if the typeclass argument is a direct superclass. *)
  cl_context : ((global_reference * bool) option * rel_declaration) list; 

  (* Context of definitions and properties on defs, will not be shared *)
  cl_props : rel_context;

  (* The methods implementations of the typeclass as projections. Some may be undefinable due to 
     sorting restrictions. *)
  cl_projs : (identifier * constant option) list;
}

type instance

val instances : global_reference -> instance list
val typeclasses : unit -> typeclass list
val all_instances : unit -> instance list

val add_class : typeclass -> unit

val new_instance : typeclass -> int option -> bool -> constant -> instance
val add_instance : instance -> unit

val class_info : global_reference -> typeclass (* raises a UserError if not a class *)


(* These raise a UserError if not a class. *)
val dest_class_app : env -> constr -> typeclass * constr list

(* Just return None if not a class *)
val class_of_constr : constr -> typeclass option
  
val instance_impl : instance -> constant

val is_class : global_reference -> bool
val is_instance : global_reference -> bool
val is_method : constant -> bool

val is_implicit_arg : hole_kind -> bool

(* Returns the term and type for the given instance of the parameters and fields
   of the type class. *)

val instance_constructor : typeclass -> constr list -> constr * types

(* Use evar_extra for marking resolvable evars. *)
val bool_in : bool -> Dyn.t
val bool_out : Dyn.t -> bool

val is_resolvable : evar_info -> bool
val mark_unresolvable : evar_info -> evar_info
val mark_unresolvables : evar_map -> evar_map
val is_class_evar : evar_info -> bool

val resolve_typeclasses : ?onlyargs:bool -> ?split:bool -> ?fail:bool -> 
  env -> evar_defs -> evar_defs
val resolve_one_typeclass : env -> evar_map -> types -> constr

val register_add_instance_hint : (constant -> int option -> unit) -> unit
val add_instance_hint : constant -> int option -> unit

val solve_instanciations_problem : (env -> evar_defs -> bool -> bool -> bool -> evar_defs) ref
val solve_instanciation_problem : (env -> evar_map -> types -> constr) ref
