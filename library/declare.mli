
(* $Id$ *)

(*i*)
open Names
open Term
open Sign
open Declarations
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

type section_variable_entry =
  | SectionLocalDef of constr
  | SectionLocalDecl of constr

type sticky = bool

type variable_declaration = section_variable_entry * strength * sticky
val declare_variable : identifier -> variable_declaration -> unit

type constant_declaration = constant_entry * strength
val declare_constant : identifier -> constant_declaration -> unit

val declare_parameter : identifier -> constr -> unit

val declare_mind : mutual_inductive_entry -> section_path

val declare_eliminations : section_path -> int -> unit

val make_strength : string list -> strength
val make_strength_0 : unit -> strength
val make_strength_1 : unit -> strength
val make_strength_2 : unit -> strength

(*s Corresponding test and access functions. *)

val is_constant : section_path -> bool
val constant_strength : section_path -> strength
val constant_or_parameter_strength : section_path -> strength

val is_variable : identifier -> bool
val out_variable : section_path -> named_declaration * strength * sticky
val variable_strength : identifier -> strength


(*s [global_operator k id] returns the operator (constant, inductive or
    construtor) corresponding to [id] in global environment, together
    with its definition environment. *)

val global_operator : path_kind -> identifier -> global_reference * named_context

(*s [global_reference k id] returns the object corresponding to
    the name [id] in the global environment. It may be a constant, 
    an inductive, a construtor or a variable. It is instanciated
    on the current environment of variables. [Nametab.sp_of_id] is used
    to find the corresponding object. 
    [construct_reference] is a version which looks for variables in a 
    given environment instead of looking in the current global environment. *)

val global_sp_reference : section_path -> identifier -> constr

val global_reference : path_kind -> identifier -> constr
val global_reference_imps : path_kind -> identifier -> constr * int list

val construct_reference : Environ.env -> path_kind -> identifier -> constr

val is_global : identifier -> bool

val path_of_inductive_path : inductive_path -> section_path
val path_of_constructor_path : constructor_path -> section_path

(* Look up function for the default elimination constant *)
val elimination_suffix : sorts -> string
val lookup_eliminator : Environ.env -> section_path -> sorts -> constr
