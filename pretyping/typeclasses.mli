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
  cl_name : identifier; (* Name of the class *)
  cl_context : named_context; (* Context in which superclasses and params are typed (usually types) *)
  cl_super : named_context; (* Superclasses applied to some of the params *)
  cl_params : named_context; (* Context of the real parameters (types and operations) *)
(*   cl_defs : rel_context; (\* Context of the definitions (usually functions), which may be shared *\) *)
  cl_props : named_context; (* Context of the properties on defs, in Prop, will not be shared *)
  cl_impl : inductive; (* The class implementation: a record parameterized by params and defs *)
}

type instance = {
  is_class: typeclass;
  is_name: identifier; (* Name of the instance *)
(*   is_params: named_context; (\* Context of the parameters, instanciated *\) *)
(*   is_super: named_context; (\* The corresponding superclasses *\) *)
  is_impl: constant; 
(*   is_add_hint : unit -> unit; (\* Hook to add an hint for the instance *\) *)
}
  
val instances : Libnames.reference -> instance list
val typeclasses : unit -> typeclass list
val add_class : typeclass -> unit
val add_instance : instance -> unit

val class_info : identifier -> typeclass (* raises Not_found *)
val class_of_inductive : inductive -> typeclass (* raises Not_found *)

val resolve_one_typeclass : env -> types -> types (* Raises Not_found *)
val resolve_one_typeclass_evd : env -> evar_defs ref -> types -> types (* Raises Not_found *)

val is_class : inductive -> bool

val class_of_constr : constr -> typeclass option

val resolve_typeclass : env -> evar -> evar_info -> evar_defs * bool -> evar_defs * bool
val resolve_typeclasses : ?check:bool -> env -> evar_map -> evar_defs -> evar_defs

val solve_instanciation_problem : (env -> evar_defs -> existential_key -> evar_info -> evar_defs * bool) ref

type substitution = (identifier * constr) list

val substitution_of_named_context : 
  evar_defs ref -> env -> identifier -> int ->
  substitution -> named_context -> substitution

val nf_substitution : evar_map -> substitution -> substitution
