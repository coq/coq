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

type variable_declaration = dir_path * section_variable_entry * logical_kind

val declare_variable : variable -> variable_declaration -> object_name

(* Declaration of global constructions *)
(* i.e. Definition/Theorem/Axiom/Parameter/... *)

type constant_declaration = constant_entry * logical_kind

(* [declare_constant id cd] declares a global declaration
   (constant/parameter) with name [id] in the current section; it returns
   the full path of the declaration *)
val declare_constant :
 identifier -> constant_declaration -> constant

val declare_internal_constant :
  identifier -> constant_declaration -> constant

(* [declare_mind me] declares a block of inductive types with
   their constructors in the current section; it returns the path of
   the whole block (boolean must be true iff it is a record) *)
val declare_mind : bool -> mutual_inductive_entry -> object_name

val strength_min : strength * strength -> strength
val string_of_strength : strength -> string

(*s Corresponding test and access functions. *)

val is_constant : section_path -> bool
val constant_strength : section_path -> strength
val constant_kind : section_path -> logical_kind

val get_variable : variable -> named_declaration
val variable_strength : variable -> strength 
val variable_kind : variable -> logical_kind
val find_section_variable : variable -> section_path
val last_section_hyps : dir_path -> identifier list
val clear_proofs : named_context -> Environ.named_context_val

(*s Global references *)

val strength_of_global : global_reference -> strength

(* hooks for XML output *)
val set_xml_declare_variable : (object_name -> unit) -> unit
val set_xml_declare_constant : (bool * constant -> unit) -> unit
val set_xml_declare_inductive : (bool * object_name -> unit) -> unit
