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

  (* Context in which the definitions are typed. Includes both typeclass parameters and superclasses. The boolean indicates if the 
     typeclass argument is a direct superclass. *)
  cl_context : ((global_reference * bool) option * named_declaration) list; 

  cl_params : int; (* This is the length of the suffix of the context which should be considered explicit parameters. *)

  (* Context of definitions and properties on defs, will not be shared *)
  cl_props : named_context;

  (* The methods implementations of the typeclass as projections. *)
  cl_projs : (identifier * constant) list;
}

type instance

val instance_impl : instance -> constant

val new_instance : typeclass -> int option -> bool -> constant -> instance
  
val instances : global_reference -> instance list
val typeclasses : unit -> typeclass list
val add_class : typeclass -> unit
val add_instance : instance -> unit

val register_add_instance_hint : (constant -> int option -> unit) -> unit
val add_instance_hint : constant -> int option -> unit

val class_info : global_reference -> typeclass (* raises a UserError if not a class *)
val is_class : global_reference -> bool
val class_of_constr : constr -> typeclass option
val dest_class_app : constr -> typeclass * constr array (* raises a UserError if not a class *)

val is_instance : global_reference -> bool
val is_method : constant -> bool

(* Returns the term and type for the given instance of the parameters and fields
   of the type class. *)
val instance_constructor : typeclass -> constr list -> constr * types

val resolve_one_typeclass : env -> types -> types (* Raises Not_found *)
val resolve_one_typeclass_evd : env -> evar_defs ref -> types -> types (* Raises Not_found *)
val resolve_typeclass : env -> evar -> evar_info -> evar_defs * bool -> evar_defs * bool

(* Use evar_extra for marking resolvable evars. *)
val bool_in : bool -> Dyn.t
val bool_out : Dyn.t -> bool

val is_resolvable : evar_info -> bool
val mark_unresolvable : evar_info -> evar_info

val resolve_typeclasses : ?onlyargs:bool -> ?fail:bool -> env -> evar_map -> evar_defs -> evar_defs

val solve_instanciation_problem : (env -> evar_defs -> existential_key -> evar_info -> evar_defs * bool) ref
val solve_instanciations_problem : (env -> evar_defs -> bool -> bool -> evar_defs) ref

type substitution = (identifier * constr) list

val substitution_of_named_context : 
  evar_defs ref -> env -> identifier -> int ->
  substitution -> named_context -> substitution

val nf_substitution : evar_map -> substitution -> substitution

val is_implicit_arg : hole_kind -> bool

(* debug *)

(* val subst :  *)
(*     'a * Mod_subst.substitution * *)
(*     ((Libnames.global_reference, typeclass) Gmap.t * 'b * *)
(*      ('c, instance list) Gmap.t) -> *)
(*     (Libnames.global_reference, typeclass) Gmap.t * 'b * *)
(*     ('c, instance list) Gmap.t *)

