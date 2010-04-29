(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(*i $Id$ i*)

(** This file builds schemes relative to equality inductive types *)

open Names
open Term
open Environ
open Ind_tables

(** Builds a left-to-right rewriting scheme for an equality type *)

val rew_l2r_dep_scheme_kind : individual scheme_kind
val rew_l2r_scheme_kind : individual scheme_kind
val rew_l2r_forward_dep_scheme_kind : individual scheme_kind
val rew_r2l_forward_dep_scheme_kind : individual scheme_kind
val rew_r2l_dep_scheme_kind : individual scheme_kind
val rew_r2l_scheme_kind : individual scheme_kind
val rew_asym_scheme_kind : individual scheme_kind

val build_r2l_rew_scheme : bool -> env -> inductive -> sorts_family -> constr
val build_l2r_rew_scheme : bool -> env -> inductive -> sorts_family -> constr
val build_l2r_forward_rew_scheme :
  bool -> env -> inductive -> sorts_family -> constr
val build_r2l_forward_rew_scheme :
  bool -> env -> inductive -> sorts_family -> constr

(** Builds a symmetry scheme for a symmetrical equality type *)

val build_sym_scheme : env -> inductive -> constr
val sym_scheme_kind : individual scheme_kind

val build_sym_involutive_scheme : env -> inductive -> constr
val sym_involutive_scheme_kind : individual scheme_kind

(** Builds a congruence scheme for an equality type *)

val congr_scheme_kind : individual scheme_kind
val build_congr : env -> constr * constr -> inductive -> constr
