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
open Inductiveops
open Environ
open Evd
(*i*)

(* Eliminations. *)

(* These functions build elimination predicate for Case tactic *)

val make_case_dep : env -> evar_map -> inductive -> sorts_family -> constr
val make_case_nodep : env -> evar_map -> inductive -> sorts_family -> constr
val make_case_gen : env -> evar_map -> inductive -> sorts_family -> constr

(* This builds an elimination scheme associated (using the own arity
   of the inductive) *)

val build_indrec : env -> evar_map -> inductive -> constr
val instanciate_indrec_scheme : sorts -> int -> constr -> constr

(* This builds complex [Scheme] *)

val build_mutual_indrec : 
  env -> evar_map ->
    (inductive * mutual_inductive_body * one_inductive_body
    * bool * sorts_family) list
    -> constr list

(* These are for old Case/Match typing *)

val type_rec_branches : bool -> env -> evar_map -> inductive_type
  -> unsafe_judgment -> constr -> constr array * constr
val make_rec_branch_arg : 
  env -> evar_map ->
    int * ('b * constr) option array * int ->
    constr -> constructor_summary -> wf_paths list -> constr

(* *)
val declare_eliminations : mutual_inductive -> unit
val lookup_eliminator : inductive -> sorts_family -> constr
val elimination_suffix : sorts_family -> string
val make_elimination_ident : identifier -> sorts_family -> identifier
