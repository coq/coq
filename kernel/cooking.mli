(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Names
open Term
open Declarations
open Environ
open Univ

(*s Cooking the constants. *)

type modification_action = ABSTRACT | ERASE

type 'a modification =
  | NOT_OCCUR
  | DO_ABSTRACT of 'a * modification_action list
  | DO_REPLACE of constant_body

type work_list =
    (section_path * section_path modification) list
    * (inductive_path * inductive_path modification) list
    * (constructor_path * constructor_path modification) list

type recipe = {
  d_from : constant_body;
  d_abstract : identifier list;
  d_modlist : work_list }

val cook_constant :
  env -> recipe -> constr option * constr * constraints * bool

(*s Utility functions used in module [Discharge]. *)

val expmod_constr : env -> work_list -> constr -> constr
val expmod_type : env -> work_list -> types -> types


