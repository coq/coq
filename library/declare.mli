(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Libnames
open Term
open Entries
open Decl_kinds

(** This module provides the official functions to declare new variables,
   parameters, constants and inductive types. Using the following functions
   will add the entries in the global environment (module [Global]), will
   register the declarations in the library (module [Lib]) --- so that the
   reset works properly --- and will fill some global tables such as
   [Nametab] and [Impargs]. *)

(** Declaration of local constructions (Variable/Hypothesis/Local) *)

type section_variable_entry =
  | SectionLocalDef of definition_entry
  | SectionLocalAssum of types Univ.in_universe_context_set * polymorphic * bool (** Implicit status *)

type variable_declaration = DirPath.t * section_variable_entry * logical_kind

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

(* Defaut definition entries, transparent with no secctx or proj information *)
val definition_entry : ?opaque:bool -> ?inline:bool -> ?types:types -> 
  ?poly:polymorphic -> ?univs:Univ.universe_context -> ?eff:Declareops.side_effects ->
  constr -> definition_entry

val declare_constant :
 ?internal:internal_flag -> ?local:bool -> Id.t -> constant_declaration -> constant

val declare_definition : 
  ?internal:internal_flag -> ?opaque:bool -> ?kind:definition_object_kind ->
  ?local:bool -> ?poly:polymorphic -> Id.t -> ?types:constr -> 
  constr Univ.in_universe_context_set -> constant

(** Since transparent constant's side effects are globally declared, we
 *  need that *)
val set_declare_scheme :
  (string -> (inductive * constant) array -> unit) -> unit

(** [declare_mind me] declares a block of inductive types with
   their constructors in the current section; it returns the path of
   the whole block and a boolean indicating if it is a primitive record. *)
val declare_mind : mutual_inductive_entry -> object_name * bool

(** Declaration messages *)

val definition_message : Id.t -> unit
val assumption_message : Id.t -> unit
val fixpoint_message : int array option -> Id.t list -> unit
val cofixpoint_message : Id.t list -> unit
val recursive_message : bool (** true = fixpoint *) ->
  int array option -> Id.t list -> unit

val exists_name : Id.t -> bool



(** Global universe names and constraints *)

val do_universe : Id.t Loc.located list -> unit
val do_constraint : (Id.t Loc.located * Univ.constraint_type * Id.t Loc.located) list -> unit
