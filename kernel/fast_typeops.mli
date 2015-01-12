(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Univ
open Term
open Context
open Environ
open Entries
open Declarations

(** {6 Typing functions (not yet tagged as safe) }
    
    They return unsafe judgments that are "in context" of a set of 
    (local) universe variables (the ones that appear in the term)
    and associated constraints. In case of polymorphic definitions,
    these variables and constraints will be generalized.
 *)


val infer      : env -> constr       -> unsafe_judgment
val infer_v    : env -> constr array -> unsafe_judgment array
val infer_type : env -> types        -> unsafe_type_judgment
