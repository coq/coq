
(*i $Id$ i*)

open Names
open Term
open Miniml

(*s Renaming issues. *)

val get_global_name : identifier -> identifier

type renaming_function = identifier list -> name -> identifier

module type Renaming = sig
  val rename_type_parameter : renaming_function
  val rename_type : renaming_function
  val rename_term : renaming_function
  val rename_global_type : renaming_function
  val rename_global_constructor : renaming_function
  val rename_global_term : renaming_function
end

(*s The extraction functor. It returns a single function [extract]
    translating a piece of CIC environment into a list of ML declarations.
    The boolean indicates whether cofix are allowed or not. *)

module type Translation = sig
  val extract : bool -> global_reference list -> ml_decl list
end

module Make : functor (R : Renaming) -> Translation


