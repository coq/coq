(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This files implements auto and related automation tactics *)

open Names
open EConstr
open Pattern
open Hints
open Tactypes

val compute_secvars : Proofview.Goal.t -> Id.Pred.t

val default_search_depth : int ref

val auto_flags_of_state : TransparentState.t -> Unification.unify_flags

(** Try unification with the precompiled clause, then use registered Apply *)
val unify_resolve : Unification.unify_flags -> hint -> unit Proofview.tactic

(** [ConclPattern concl pat tacast]:
   if the term concl matches the pattern pat, (in sense of
   [Pattern.somatches], then replace [?1] [?2] metavars in tacast by the
   right values to build a tactic *)

val conclPattern : constr -> constr_pattern option -> Genarg.glob_generic_argument -> unit Proofview.tactic

(** The Auto tactic *)

(** The use of the "core" database can be de-activated by passing
    "nocore" amongst the databases. *)

val auto : ?debug:debug ->
  int -> delayed_open_constr list -> hint_db_name list -> unit Proofview.tactic

(** Auto with more delta. *)

(** auto with default search depth and with the hint database "core" *)
val default_auto : unit Proofview.tactic

(** auto with all hint databases *)
val full_auto : ?debug:debug ->
  int -> delayed_open_constr list -> unit Proofview.tactic

(** auto with default search depth and with all hint databases *)
val default_full_auto : unit Proofview.tactic

(** The generic form of auto (second arg [None] means all bases) *)
val gen_auto : ?debug:debug ->
  int option -> delayed_open_constr list -> hint_db_name list option -> unit Proofview.tactic

(** The hidden version of auto *)
val h_auto   : ?debug:debug ->
  int option -> delayed_open_constr list -> hint_db_name list option -> unit Proofview.tactic

(** Trivial *)

val trivial : ?debug:debug ->
  delayed_open_constr list -> hint_db_name list -> unit Proofview.tactic
val gen_trivial : ?debug:debug ->
  delayed_open_constr list -> hint_db_name list option -> unit Proofview.tactic
val full_trivial : ?debug:debug ->
  delayed_open_constr list -> unit Proofview.tactic
val h_trivial : ?debug:debug ->
  delayed_open_constr list -> hint_db_name list option -> unit Proofview.tactic
