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
open Term
open Sign
open Declarations
open Entries
open Indtypes
open Safe_typing
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

val declare_variable : variable -> variable_declaration -> object_name

(* Declaration from Discharge *)
val redeclare_variable :
 variable -> Dischargedhypsmap.discharged_hyps -> variable_declaration -> unit

(* Declaration of global constructions *)
(* i.e. Definition/Theorem/Axiom/Parameter/... *)

type constant_declaration = constant_entry * global_kind

(* [declare_constant id cd] declares a global declaration
   (constant/parameter) with name [id] in the current section; it returns
   the full path of the declaration *)
val declare_constant : identifier -> constant_declaration -> object_name

val declare_internal_constant :
  identifier -> constant_declaration -> object_name

val redeclare_constant :
 identifier -> Dischargedhypsmap.discharged_hyps -> 
      Cooking.recipe * global_kind -> unit

(* [declare_mind me] declares a block of inductive types with
   their constructors in the current section; it returns the path of
   the whole block (boolean must be true iff it is a record) *)
val declare_mind : bool -> mutual_inductive_entry -> object_name

(* Declaration from Discharge *)
val redeclare_inductive :
 Dischargedhypsmap.discharged_hyps -> mutual_inductive_entry -> object_name

val out_inductive : Libobject.obj -> mutual_inductive_entry 

val strength_min : strength * strength -> strength
val string_of_strength : strength -> string

(*s Corresponding test and access functions. *)

val is_constant : section_path -> bool
val constant_strength : section_path -> strength
val constant_kind : section_path -> global_kind

val out_variable : Libobject.obj -> identifier * variable_declaration
val get_variable : variable -> named_declaration
val get_variable_with_constraints : 
  variable -> named_declaration * Univ.constraints
val variable_strength : variable -> strength 
val variable_kind : variable -> local_kind
val find_section_variable : variable -> section_path
val last_section_hyps : dir_path -> identifier list
val clear_proofs : named_context -> named_context

(*s Global references *)

val context_of_global_reference : global_reference -> section_context
val strength_of_global : global_reference -> strength

(* hooks for XML output *)
val set_xml_declare_variable : (object_name -> unit) -> unit
val set_xml_declare_constant : (bool * object_name -> unit) -> unit
val set_xml_declare_inductive : (bool * object_name -> unit) -> unit
