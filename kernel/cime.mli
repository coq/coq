(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Declarations
open Term
open Names

(* environment for CiME *)
type env

(* empty environment *)
val empty_env : env

(* add symbol and inductive *)
val add_symbol : constant_body KNmap.t -> env -> env
val add_inductive : mutual_inductive_body KNmap.t -> env -> env

(* add rules *)
val add_rules : rules_body -> env -> env

(* say if the addition of rules preserves confluence *)
val is_confluent : env -> (constr * constr) list -> bool

(* return None if [t] is already in normal form
   return [Some t'] where [t'] is the normal form of [t] otherwise *)
val normalize : env -> constr -> constr option

(* give the normal form *)
val nf : env -> constr -> constr

