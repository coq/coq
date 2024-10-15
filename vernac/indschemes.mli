(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Environ

type resolved_scheme = Names.Id.t CAst.t * Indrec.dep_flag * Names.inductive * Sorts.family

(** See also Auto_ind_decl, Indrec, Eqscheme, Ind_tables, ... *)

(** Build and register the boolean equalities associated to an inductive type *)

val declare_beq_scheme : ?locmap:Ind_tables.Locmap.t -> MutInd.t -> unit

val declare_eq_decidability : ?locmap:Ind_tables.Locmap.t -> MutInd.t -> unit

(** Build and register a congruence scheme for an equality-like inductive type *)

val declare_congr_scheme : ?loc:Loc.t -> inductive -> unit

(** Build and register rewriting schemes for an equality-like inductive type *)

val declare_rewriting_schemes : ?loc:Loc.t -> inductive -> unit

(** Mutual Minimality/Induction scheme.
    [force_mutual] forces the construction of eliminators having the same predicates and
    methods even if some of the inductives are not recursive.
    By default it is [false] and some of the eliminators are defined as simple case analysis.
    By default [isrec] is [true].
 *)

val do_mutual_induction_scheme : ?force_mutual:bool
  -> Environ.env -> ?isrec:bool -> resolved_scheme list -> unit

(** Main calls to interpret the Scheme command *)

val do_scheme : Environ.env -> (Names.Id.t CAst.t option * Vernacexpr.scheme) list -> unit

(** Main call to Scheme Equality command *)

val do_scheme_equality : ?locmap:Ind_tables.Locmap.t -> Vernacexpr.equality_scheme_type -> Libnames.qualid Constrexpr.or_by_notation -> unit

(** Combine a list of schemes into a conjunction of them *)

val build_combined_scheme : env -> Constant.t list -> Evd.evar_map * constr * types

val do_combined_scheme : lident -> Constant.t list -> unit

(** Hook called at each inductive type definition *)

val declare_default_schemes : ?locmap:Ind_tables.Locmap.t -> MutInd.t -> unit
