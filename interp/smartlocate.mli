(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

open Util
open Names
open Libnames
open Genarg

(** [locate_global_with_alias] locates global reference possibly following
   a notation if this notation has a role of aliasing; raise Not_found
   if not bound in the global env; raise an error if bound to a
   syntactic def that does not denote a reference *)

val locate_global_with_alias : qualid located -> global_reference

(** Extract a global_reference from a reference that can be an "alias" *)
val global_of_extended_global : extended_global_reference -> global_reference

(** Locate a reference taking into account possible "alias" notations *)
val global_with_alias : reference -> global_reference

(** The same for inductive types *)
val global_inductive_with_alias : reference -> inductive

(** Locate a reference taking into account notations and "aliases" *)
val smart_global : reference or_by_notation -> global_reference

(** The same for inductive types *)
val smart_global_inductive : reference or_by_notation -> inductive

