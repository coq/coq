(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Declarations
open Inductive
open Environ
open Evd
(*i*)

(* Eliminations. *)

(* These functions build elimination predicate for Case tactic *)

val make_case_dep : env -> 'a evar_map -> inductive -> sorts -> constr
val make_case_nodep : env -> 'a evar_map -> inductive -> sorts -> constr
val make_case_gen : env -> 'a evar_map -> inductive -> sorts -> constr

(* This builds an elimination scheme associated (using the own arity
   of the inductive) *)

val build_indrec : env -> 'a evar_map -> inductive_instance -> constr
val instanciate_indrec_scheme : sorts -> int -> constr -> constr

(* This builds complex [Scheme] *)

val build_mutual_indrec : 
  env -> 'a evar_map -> (inductive * bool * sorts) list -> constr list

(* These are for old Case/Match typing *)

val type_rec_branches : bool -> env -> 'c evar_map -> inductive_type
  -> constr -> constr -> constr -> constr array * constr
val make_rec_branch_arg : 
  env -> 'a evar_map ->
    int * ('b * constr) option array * int ->
    constr -> constructor_summary -> recarg list -> constr
