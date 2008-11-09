(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Declarations
open Inductiveops
open Environ
open Evd
(*i*)

(* Errors related to recursors building *)

type recursion_scheme_error =
  | NotAllowedCaseAnalysis of (*isrec:*) bool * sorts * inductive
  | NotMutualInScheme of inductive * inductive

exception RecursionSchemeError of recursion_scheme_error

(** Eliminations *)

(* These functions build elimination predicate for Case tactic *)

val make_case_dep : env -> evar_map -> inductive -> sorts_family -> constr
val make_case_nodep : env -> evar_map -> inductive -> sorts_family -> constr
val make_case_gen : env -> evar_map -> inductive -> sorts_family -> constr

(* This builds an elimination scheme associated (using the own arity
   of the inductive) *)

val build_indrec : env -> evar_map -> inductive -> constr
val instantiate_indrec_scheme : sorts -> int -> constr -> constr
val instantiate_type_indrec_scheme : sorts -> int -> constr -> types ->
  constr * types

(** Complex recursion schemes [Scheme] *)

val build_mutual_indrec : 
  env -> evar_map ->
    (inductive * mutual_inductive_body * one_inductive_body
    * bool * sorts_family) list
    -> constr list

(** Old Case/Match typing *)

val type_rec_branches : bool -> env -> evar_map -> inductive_type
  -> constr -> constr -> constr array * constr
val make_rec_branch_arg : 
  env -> evar_map ->
    int * ('b * constr) option array * int ->
    constr -> constructor_summary -> wf_paths list -> constr

(** Recursor names utilities *)

val lookup_eliminator : inductive -> sorts_family -> constr
val elimination_suffix : sorts_family -> string
val make_elimination_ident : identifier -> sorts_family -> identifier



