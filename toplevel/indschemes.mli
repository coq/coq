(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Names
open Term
open Environ
open Vernacexpr
open Misctypes

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
  (Id.t located * bool * inductive * glob_sort) list -> unit

(** Main calls to interpret the Scheme command *)

val do_scheme : (Id.t located option * scheme) list -> unit

(** Combine a list of schemes into a conjunction of them *)

val build_combined_scheme : env -> constant list -> constr * types

val do_combined_scheme : Id.t located -> Id.t located list -> unit

(** Hook called at each inductive type definition *)

val declare_default_schemes : mutual_inductive -> unit
