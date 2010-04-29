(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(*i $Id$ i*)

open Names
open Term
open Declarations
open Inductiveops
open Environ
open Evd

(** Errors related to recursors building *)

type recursion_scheme_error =
  | NotAllowedCaseAnalysis of (*isrec:*) bool * sorts * inductive
  | NotMutualInScheme of inductive * inductive

exception RecursionSchemeError of recursion_scheme_error

(** Eliminations *)

type dep_flag = bool

(** Build a case analysis elimination scheme in some sort family *)

val build_case_analysis_scheme : env -> evar_map -> inductive ->
      dep_flag -> sorts_family -> constr

(** Build a dependent case elimination predicate unless type is in Prop *)

val build_case_analysis_scheme_default : env -> evar_map -> inductive ->
      sorts_family -> constr

(** Builds a recursive induction scheme (Peano-induction style) in the same
   sort family as the inductive family; it is dependent if not in Prop *)

val build_induction_scheme : env -> evar_map -> inductive ->
      dep_flag -> sorts_family -> constr

(** Builds mutual (recursive) induction schemes *)

val build_mutual_induction_scheme :
  env -> evar_map -> (inductive * dep_flag * sorts_family) list -> constr list

(** Scheme combinators *)

(** [modify_sort_scheme s n c] modifies the quantification sort of
   scheme c whose predicate is abstracted at position [n] of [c] *)

val modify_sort_scheme : sorts -> int -> constr -> constr

(** [weaken_sort_scheme s n c t] derives by subtyping from [c:t]
   whose conclusion is quantified on [Type] at position [n] of [t] a
   scheme quantified on sort [s] *)

val weaken_sort_scheme : sorts -> int -> constr -> types -> constr * types

(** Recursor names utilities *)

val lookup_eliminator : inductive -> sorts_family -> constr
val elimination_suffix : sorts_family -> string
val make_elimination_ident : identifier -> sorts_family -> identifier

val case_suffix : string
