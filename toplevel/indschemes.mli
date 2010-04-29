(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(*i $Id$ i*)

open Util
open Names
open Term
open Environ
open Libnames
open Rawterm
open Genarg
open Vernacexpr
open Ind_tables

(** See also Auto_ind_decl, Indrec, Eqscheme, Ind_tables, ... *)

(** Build and register the boolean equalities associated to an inductive type *)

val declare_beq_scheme : mutual_inductive -> unit

val declare_eq_decidability : mutual_inductive -> unit

(** Build and register a congruence scheme for an equality-like inductive type *)

val declare_congr_scheme : inductive -> unit

(** Build and register rewriting schemes for an equality-like inductive type *)

val declare_rewriting_schemes : inductive -> unit

(** Mutual Minimality/Induction scheme *)

val do_mutual_induction_scheme :
  (identifier located * bool * inductive * rawsort) list -> unit

(** Main calls to interpret the Scheme command *)

val do_scheme : (identifier located option * scheme) list -> unit

(** Combine a list of schemes into a conjunction of them *)

val build_combined_scheme : env -> constant list -> constr * types

val do_combined_scheme : identifier located -> identifier located list -> unit

(** Hook called at each inductive type definition *)

val declare_default_schemes : mutual_inductive -> unit
