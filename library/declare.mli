
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

val declare_variable : identifier -> constr -> unit

val declare_parameter : identifier -> constr -> unit

val declare_constant : identifier -> constant_entry -> unit

val declare_mind : mutual_inductive_entry -> unit

