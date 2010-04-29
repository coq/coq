(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

open Term
open Names
open Libnames
open Mod_subst
open Sign
open Proof_type
open Ind_tables

(** This file is about the automatic generation of schemes about
    decidable equality,
    @author Vincent Siles
    Oct 2007 *)

(** {6 Build boolean equality of a block of mutual inductive types } *)

exception EqNotFound of inductive * inductive
exception EqUnknown of string
exception UndefinedCst of string
exception InductiveWithProduct
exception InductiveWithSort
exception ParameterWithoutEquality of constant
exception NonSingletonProp of inductive

val beq_scheme_kind : mutual scheme_kind
val build_beq_scheme : mutual_inductive -> constr array

(** {6 Build equivalence between boolean equality and Leibniz equality } *)

val lb_scheme_kind : mutual scheme_kind
val make_lb_scheme : mutual_inductive -> constr array

val bl_scheme_kind : mutual scheme_kind
val make_bl_scheme : mutual_inductive -> constr array

(** {6 Build decidability of equality } *)

val eq_dec_scheme_kind : mutual scheme_kind
val make_eq_decidability : mutual_inductive -> constr array
