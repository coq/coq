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
open Indtypes
open Safe_typing
open Library
open Nametab
open Decl_kinds
(*i*)

(* This module provides the official functions to declare new variables, 
   parameters, constants and inductive types. Using the following functions
   will add the entries in the global environment (module [Global]), will
   register the declarations in the library (module [Lib]) --- so that the
   reset works properly --- and will fill some global tables such as 
   [Nametab] and [Impargs]. *)

open Nametab

(* Declaration of local constructions (Variable/Hypothesis/Local) *)

type section_variable_entry =
  | SectionLocalDef of constr * types option * bool (* opacity *)
  | SectionLocalAssum of types

type variable_declaration = dir_path * section_variable_entry * local_kind

val declare_variable : variable -> variable_declaration -> section_path

(* Declaration from Discharge *)
val redeclare_variable :
 variable -> Dischargedhypsmap.discharged_hyps -> variable_declaration 
 -> section_path

(* Declaration of global constructions *)
(* i.e. Definition/Theorem/Axiom/Parameter/... *)

type constant_declaration = global_declaration * global_kind

(* [declare_constant id cd] declares a global declaration
   (constant/parameter) with name [id] in the current section; it returns
   the full path of the declaration *)
val declare_constant : identifier -> constant_declaration -> constant

val redeclare_constant :
 constant -> Dischargedhypsmap.discharged_hyps -> 
      Cooking.recipe * global_kind -> unit

(*
val declare_parameter : identifier -> constr -> constant
*)

(* [declare_mind me] declares a block of inductive types with
   their constructors in the current section; it returns the path of
   the whole block *)
val declare_mind : mutual_inductive_entry -> mutual_inductive

(* Declaration from Discharge *)
val redeclare_inductive :
 Dischargedhypsmap.discharged_hyps -> mutual_inductive_entry
  -> mutual_inductive

val out_inductive : Libobject.obj -> mutual_inductive_entry 

val strength_min : strength * strength -> strength
val string_of_strength : strength -> string

(*s Corresponding test and access functions. *)

val is_constant : section_path -> bool
val constant_strength : constant -> strength
val constant_kind : constant -> global_kind

val out_variable : Libobject.obj -> identifier * variable_declaration
val get_variable : variable -> named_declaration
val get_variable_with_constraints : 
  variable -> named_declaration * Univ.constraints
val variable_strength : variable -> strength 
val find_section_variable : variable -> section_path
val last_section_hyps : dir_path -> identifier list

(*s Global references *)

val context_of_global_reference : global_reference -> section_context

(* Turn a global reference into a construction *)
val constr_of_reference : global_reference -> constr

(* Turn a construction denoting a global into a reference;
   raise [Not_found] if not a global *)
val reference_of_constr : constr -> global_reference

val global_qualified_reference : Nametab.qualid -> constr
val global_absolute_reference : section_path -> constr
val global_reference_in_absolute_module : dir_path -> identifier -> constr

val construct_qualified_reference : Nametab.qualid -> constr
val construct_absolute_reference : section_path -> constr

(* This should eventually disappear *)
(*  [construct_reference] returns the object corresponding to
    the name [id] in the global environment. It looks also for variables in a 
    given environment instead of looking in the current global environment. *)
val global_reference : identifier -> constr
val construct_reference : Environ.env -> identifier -> constr

val is_global : identifier -> bool

val strength_of_global : global_reference -> strength

val library_part : global_reference -> dir_path

(* hooks for XML output *)
val set_xml_declare_variable : (section_path -> unit) -> unit
val set_xml_declare_constant : (section_path -> unit) -> unit
val set_xml_declare_inductive : (section_path -> unit) -> unit
