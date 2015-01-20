(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Genarg
open Names
open Tacexpr

(** This module centralizes the various ways of registering tactics. *)

(** {5 Tactic notations} *)

type alias = KerName.t
(** Type of tactic alias, used in the [TacAlias] node. *)

val register_alias : alias -> glob_tactic_expr -> unit
(** Register a tactic alias. *)

val interp_alias : alias -> glob_tactic_expr
(** Recover the the body of an alias. Raises an anomaly if it does not exist. *)

(** {5 Coq tactic definitions} *)

val register_ltac : bool -> bool -> Id.t -> glob_tactic_expr -> unit
(** Register a new Ltac with the given name and body.

    The first boolean indicates whether this is done from ML side, rather than
    Coq side. If the second boolean flag is set to true, then this is a local
    definition. It also puts the Ltac name in the nametab, so that it can be
    used unqualified. *)

val redefine_ltac : bool -> KerName.t -> glob_tactic_expr -> unit
(** Replace a Ltac with the given name and body. If the boolean flag is set
    to true, then this is a local redefinition. *)

val interp_ltac : KerName.t -> glob_tactic_expr
(** Find a user-defined tactic by name. Raise [Not_found] if it is absent. *)

val is_ltac_for_ml_tactic : KerName.t -> bool

(** {5 ML tactic extensions} *)

type ml_tactic =
  typed_generic_argument list -> Geninterp.interp_sign -> unit Proofview.tactic
(** Type of external tactics, used by [TacML]. *)

val register_ml_tactic : ?overwrite:bool -> ml_tactic_name -> ml_tactic -> unit
(** Register an external tactic. *)

val interp_ml_tactic : ml_tactic_entry -> ml_tactic
(** Get the named tactic. Raises a user error if it does not exist. *)
