(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*s Extraction from Coq terms to Miniml. *)

open Names
open Term
open Declarations
open Environ
open Libnames
open Miniml

val extract_constant : env -> constant -> constant_body -> ml_decl

val extract_constant_spec : env -> constant -> constant_body -> ml_spec

val extract_with_type : env -> constant_body -> ( identifier list * ml_type ) option

val extract_fixpoint :
  env -> constant array -> (constr, types) prec_declaration -> ml_decl

val extract_inductive : env -> mutual_inductive -> ml_ind

(*s Is a [ml_decl] or a [ml_spec] logical ? *)

val logical_decl : ml_decl -> bool
val logical_spec : ml_spec -> bool
