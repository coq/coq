(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Names
open Term
open Declarations
open Environ
open Univ

(*s Cooking the constants. *)

type 'a modification =
  | NOT_OCCUR
  | DO_ABSTRACT of 'a * constr array
  | DO_REPLACE of constant_body

type work_list =
    (constant * constant modification) list
    * (inductive * inductive modification) list
    * (constructor * constructor modification) list

type recipe = {
  d_from : constant_body;
  d_abstract : identifier list;
  d_modlist : work_list }

val cook_constant :
  env -> recipe -> constr_substituted option * constr * constraints * bool

(*s Utility functions used in module [Discharge]. *)

val expmod_constr : work_list -> constr -> constr
val expmod_type : work_list -> types -> types


