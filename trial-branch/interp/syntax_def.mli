(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Topconstr
open Rawterm
open Libnames
(*i*)

(* Syntactic definitions. *)

val declare_syntactic_definition : bool -> identifier -> bool -> aconstr
  -> unit

val search_syntactic_definition : loc -> kernel_name -> rawconstr


(* [locate_global_with_alias] locates global reference possibly following
   a notation if this notation has a role of aliasing; raise Not_found
   if not bound in the global env; raise an error if bound to a
   syntactic def that does not denote a reference *)

val locate_global_with_alias : qualid located -> global_reference

(* Locate a reference taking into account possible "alias" notations *)
val global_with_alias : reference -> global_reference

(* The same for inductive types *)
val inductive_of_reference_with_alias : reference -> inductive

