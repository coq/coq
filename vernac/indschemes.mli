(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Environ
open Vernacexpr

(** See also Auto_ind_decl, Indrec, Eqscheme, Ind_tables, ... *)

(** Build and register the boolean equalities associated to an inductive type *)

val declare_beq_scheme : MutInd.t -> unit

val declare_eq_decidability : MutInd.t -> unit

(** Build and register a congruence scheme for an equality-like inductive type *)

val declare_congr_scheme : inductive -> unit

(** Build and register rewriting schemes for an equality-like inductive type *)

val declare_rewriting_schemes : inductive -> unit

(** Mutual Minimality/Induction scheme.
    [force_mutual] forces the construction of eliminators having the same predicates and
    methods even if some of the inductives are not recursive.
    By default it is [false] and some of the eliminators are defined as simple case analysis.
 *)

val do_mutual_induction_scheme : ?force_mutual:bool ->
  (lident * bool * inductive * Sorts.family) list -> unit

(** Main calls to interpret the Scheme command *)

val do_scheme : (lident option * scheme) list -> unit

(** Combine a list of schemes into a conjunction of them *)

val build_combined_scheme : env -> Constant.t list -> Evd.evar_map * constr * types

val do_combined_scheme : lident -> lident list -> unit

(** Hook called at each inductive type definition *)

val declare_default_schemes : MutInd.t -> unit
