(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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

(** This module provides the official functions to declare new variables,
   parameters, constants and inductive types. Using the following functions
   will add the entries in the global environment (module [Global]), will
   register the declarations in the library (module [Lib]) --- so that the
   reset works properly --- and will fill some global tables such as
   [Nametab] and [Impargs]. *)

open Nametab

(** Declaration of local constructions (Variable/Hypothesis/Local) *)

type section_variable_entry =
  | SectionLocalDef of constr * types option * bool (** opacity *)
  | SectionLocalAssum of types * bool (** Implicit status *)

type variable_declaration = dir_path * section_variable_entry * logical_kind

val declare_variable : variable -> variable_declaration -> object_name

(** Declaration of global constructions 
   i.e. Definition/Theorem/Axiom/Parameter/... *)

type constant_declaration = constant_entry * logical_kind

(** [declare_constant id cd] declares a global declaration
   (constant/parameter) with name [id] in the current section; it returns
   the full path of the declaration 

  internal specify if the constant has been created by the kernel or by the
  user, and in the former case, if its errors should be silent
   
   *)
type internal_flag =
  | KernelVerbose
  | KernelSilent
  | UserVerbose

val declare_constant :
 ?internal:internal_flag -> identifier -> constant_declaration -> constant

(** [declare_mind me] declares a block of inductive types with
   their constructors in the current section; it returns the path of
   the whole block (boolean must be true iff it is a record) *)
val declare_mind : internal_flag -> mutual_inductive_entry -> object_name

(** Hooks for XML output *)
val set_xml_declare_variable : (object_name -> unit) -> unit
val set_xml_declare_constant : (internal_flag * constant -> unit) -> unit
val set_xml_declare_inductive : (internal_flag * object_name -> unit) -> unit

(** Hook for the cache function of constants and inductives *)
val add_cache_hook : (full_path -> unit) -> unit

(** Declaration messages *)

val definition_message : identifier -> unit
val assumption_message : identifier -> unit
val fixpoint_message : int array option -> identifier list -> unit
val cofixpoint_message : identifier list -> unit
val recursive_message : bool (** true = fixpoint *) ->
  int array option -> identifier list -> unit

