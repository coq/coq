(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Names
open Libnames
open Mod_subst
open Sign
open Declarations

(* This module provides support for registering inductive scheme builders,
   declaring schemes and generating schemes on demand *)

(* A scheme is either a "mutual scheme_kind" or an "individual scheme_kind" *)

type mutual
type individual
type 'a scheme_kind

type mutual_scheme_object_function = mutual_inductive -> constr array
type individual_scheme_object_function = inductive -> constr

(* Main functions to register a scheme builder *)

val declare_mutual_scheme_object : string -> ?aux:string ->
  mutual_scheme_object_function -> mutual scheme_kind

val declare_individual_scheme_object : string -> ?aux:string ->
  individual_scheme_object_function -> individual scheme_kind

(*
val declare_scheme : 'a scheme_kind -> (inductive * constant) array -> unit
*)

(* Force generation of a (mutually) scheme with possibly user-level names *)

val define_individual_scheme : individual scheme_kind -> 
  Declare.internal_flag (* internal *) ->
  identifier option -> inductive -> constant

val define_mutual_scheme : mutual scheme_kind -> Declare.internal_flag (* internal *) ->
  (int * identifier) list -> mutual_inductive -> constant array

(* Main function to retrieve a scheme in the cache or to generate it *)
val find_scheme : 'a scheme_kind -> inductive -> constant

val check_scheme : 'a scheme_kind -> inductive -> bool
