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
open Libnames
open Tacexpr
open Geninterp
open Vernacinterp

(** This module centralizes the various ways of registering tactics. *)

(** {5 Tactic naming} *)

val push_tactic : Nametab.visibility -> full_path -> ltac_constant -> unit
val locate_tactic : qualid -> ltac_constant
val locate_extended_all_tactic : qualid -> ltac_constant list
val exists_tactic : full_path -> bool
val path_of_tactic : ltac_constant -> full_path
val shortest_qualid_of_tactic : ltac_constant -> qualid

(** {5 Tactic notations} *)

type alias = KerName.t
(** Type of tactic alias, used in the [TacAlias] node. *)

type alias_tactic =
  { alias_args: Id.t list;
    alias_body: glob_tactic_expr;
    alias_deprecation: Vernacinterp.deprecation option;
  }
(** Contents of a tactic notation *)

val register_alias : alias -> alias_tactic -> unit
(** Register a tactic alias. *)

val interp_alias : alias -> alias_tactic
(** Recover the body of an alias. Raises an anomaly if it does not exist. *)

val check_alias : alias -> bool
(** Returns [true] if an alias is defined, false otherwise. *)

(** {5 Coq tactic definitions} *)

val register_ltac : bool -> bool -> ?deprecation:deprecation -> Id.t ->
  glob_tactic_expr -> unit
(** Register a new Ltac with the given name and body.

    The first boolean indicates whether this is done from ML side, rather than
    Coq side. If the second boolean flag is set to true, then this is a local
    definition. It also puts the Ltac name in the nametab, so that it can be
    used unqualified. *)

val redefine_ltac : bool -> ?deprecation:deprecation -> KerName.t ->
  glob_tactic_expr -> unit
(** Replace a Ltac with the given name and body. If the boolean flag is set
    to true, then this is a local redefinition. *)

val interp_ltac : KerName.t -> glob_tactic_expr
(** Find a user-defined tactic by name. Raise [Not_found] if it is absent. *)

val is_ltac_for_ml_tactic : KerName.t -> bool
(** Whether the tactic is defined from ML-side *)

val tac_deprecation : KerName.t -> deprecation option
(** The tactic deprecation notice, if any *)

type ltac_entry = {
  tac_for_ml : bool;
  (** Whether the tactic is defined from ML-side *)
  tac_body : glob_tactic_expr;
  (** The current body of the tactic *)
  tac_redef : ModPath.t list;
  (** List of modules redefining the tactic in reverse chronological order *)
  tac_deprecation : deprecation option;
  (** Deprecation notice to be printed when the tactic is used *)
}

val ltac_entries : unit -> ltac_entry KNmap.t
(** Low-level access to all Ltac entries currently defined. *)

(** {5 ML tactic extensions} *)

type ml_tactic =
  Val.t list -> Geninterp.interp_sign -> unit Proofview.tactic
(** Type of external tactics, used by [TacML]. *)

val register_ml_tactic : ?overwrite:bool -> ml_tactic_name -> ml_tactic array -> unit
(** Register an external tactic. *)

val interp_ml_tactic : ml_tactic_entry -> ml_tactic
(** Get the named tactic. Raises a user error if it does not exist. *)
