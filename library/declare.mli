
(* $Id$ *)

(*i*)
open Names
open Term
open Sign
open Constant
open Inductive
(*i*)

(* This module provides the official functions to declare new variables, 
   parameters, constants and inductive types. Using the following functions
   will add the entries in the global environment (module [Global]), will
   register the declarations in the library (module [Lib]) --- so that the
   reset works properly --- and will fill some global tables such as 
   [Nametab] and [Impargs]. *)

type strength = 
  | DischargeAt of section_path 
  | NeverDischarge

val declare_variable : identifier -> constr -> unit

val declare_parameter : identifier -> constr -> unit

val declare_constant : identifier -> constant_entry -> unit

val declare_mind : mutual_inductive_entry -> unit

val declare_eliminations : section_path -> unit

val declare_syntax_constant : identifier -> constr -> unit

val make_strength : string list -> strength

(*s Corresponding test and access functions. *)

val is_constant : section_path -> bool
val constant_strength : section_path -> strength

val is_variable : identifier -> bool
val out_variable : section_path -> identifier * typed_type * strength
val variable_strength : identifier -> strength

val out_syntax_constant : identifier -> constr

(*s It also provides a function [global_reference] to construct a global
  constr (a constant, an inductive or a constructor) from an identifier.
  To do so, it first looks for the section path using [Nametab.sp_of_id] and
  then constructs the corresponding term, associated to the current 
  environment of variables. *)

val global_operator : section_path -> identifier -> sorts oper * var_context
val global_reference : path_kind -> identifier -> constr
val global_reference_imps : path_kind -> identifier -> constr * int list

val is_global : identifier -> bool

val mind_path : constr -> section_path
