(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Sign
open Declarations
open Inductive
open Library
(*i*)

(* This module provides the official functions to declare new variables, 
   parameters, constants and inductive types. Using the following functions
   will add the entries in the global environment (module [Global]), will
   register the declarations in the library (module [Lib]) --- so that the
   reset works properly --- and will fill some global tables such as 
   [Nametab] and [Impargs]. *)

type strength = 
  | NotDeclare
  | DischargeAt of dir_path
  | NeverDischarge

type section_variable_entry =
  | SectionLocalDef of constr
  | SectionLocalAssum of constr

type sticky = bool

type variable_declaration = section_variable_entry * strength * sticky

val declare_variable : identifier -> variable_declaration -> variable_path

type constant_declaration_type =
  | ConstantEntry  of constant_entry
  | ConstantRecipe of Cooking.recipe

type opacity = bool

type constant_declaration = constant_declaration_type * strength * opacity

(* [declare_constant id cd] declares a global declaration
   (constant/parameter) with name [id] in the current section; it returns
   the full path of the declaration *)
val declare_constant : identifier -> constant_declaration -> constant_path

val declare_parameter : identifier -> constr -> constant_path

(* [declare_mind me] declares a block of inductive types with
   their constructors in the current section; it returns the path of
   the whole block *)
val declare_mind : mutual_inductive_entry -> mutual_inductive_path

(* [declare_eliminations sp] declares elimination schemes associated
   to the mutual inductive block refered by [sp] *)
val declare_eliminations : mutual_inductive_path -> unit

val out_inductive : Libobject.obj -> mutual_inductive_entry 

val make_strength : dir_path -> strength
val make_strength_0 : unit -> strength
val make_strength_1 : unit -> strength
val make_strength_2 : unit -> strength

(*s Corresponding test and access functions. *)

val is_constant : section_path -> bool
val constant_strength : constant_path -> strength
val constant_or_parameter_strength : constant_path -> strength

val out_variable : Libobject.obj -> identifier * variable_declaration
val get_variable : variable_path -> named_declaration * strength * sticky
val get_variable_with_constraints : 
  variable_path -> named_declaration * Univ.constraints * strength * sticky
val variable_strength : variable_path -> strength
val find_section_variable : identifier -> variable_path
val last_section_hyps : dir_path -> identifier list

(*s [global_reference k id] returns the object corresponding to
    the name [id] in the global environment. It may be a constant, 
    an inductive, a construtor or a variable. It is instanciated
    on the current environment of variables. [Nametab.sp_of_id] is used
    to find the corresponding object. 
    [construct_reference] is a version which looks for variables in a 
    given environment instead of looking in the current global environment. *)

val context_of_global_reference : global_reference -> section_context
val instantiate_inductive_section_params : constr -> inductive_path -> constr
val implicit_section_args : global_reference -> section_path list
val extract_instance : global_reference -> constr array -> constr array

val constr_of_reference :
  'a Evd.evar_map -> Environ.env -> global_reference -> constr

val global_qualified_reference : Nametab.qualid -> constr
val global_absolute_reference : section_path -> constr
val global_reference_in_absolute_module : dir_path -> identifier -> constr

val construct_qualified_reference : Environ.env -> Nametab.qualid -> constr
val construct_absolute_reference : Environ.env -> section_path -> constr

(* This should eventually disappear *)
val global_reference : path_kind -> identifier -> constr
val construct_reference : Environ.env -> path_kind -> identifier -> constr

val is_global : identifier -> bool

val path_of_inductive_path : inductive_path -> mutual_inductive_path
val path_of_constructor_path : constructor_path -> mutual_inductive_path

(* Look up function for the default elimination constant *)
val elimination_suffix : sorts -> string
val make_elimination_ident : inductive_ident:identifier -> sorts -> identifier
val lookup_eliminator : Environ.env -> inductive -> sorts -> constr
