
(* $Id$ *)

(*i*)
open Names
open Term
open Constant
open Inductive
(*i*)

(* This module provides the official functions to declare new variables, 
   parameters, constants and inductive types. Using the following functions
   will add the entries in the global environment (module [Global]), will
   register the declarations in the library (module [Lib]) --- so that the
   reset works properly --- and will fill some global tables as [Nametab] and
   [Impargs]. *)

type strength = 
  | DischargeAt of section_path 
  | NeverDischarge

val declare_variable : identifier -> constr -> unit

val declare_parameter : identifier -> constr -> unit

val declare_constant : identifier -> constant_entry -> unit

val declare_mind : mutual_inductive_entry -> unit


(*s It also provides a function [global_reference] to construct a global
  constr (a constant, an inductive or a constructor) from an identifier.
  To do so, it first looks for the section path using [Nametab.sp_of_id] and
  then constructs the corresponding term, associated to the current 
  environment of variables. *)

val global_reference : path_kind -> identifier -> constr

val mind_path : constr -> section_path
