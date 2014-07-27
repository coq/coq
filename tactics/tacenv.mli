(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
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

(** FIXME: one day we should merge atomic tactics and user-defined ones. *)

val register_atomic_ltac : Id.t -> glob_tactic_expr -> unit
(** Register a Coq built-in tactic. Should not be used by plugins. *)

val interp_atomic_ltac : Id.t -> glob_tactic_expr
(** Find a Coq built-in tactic by name. Raise [Not_found] if it is absent. *)

val register_ltac :
  Vernacexpr.locality_flag -> bool -> (Libnames.reference * bool * raw_tactic_expr) list -> unit

val interp_ltac : KerName.t -> glob_tactic_expr
(** Find a user-defined tactic by name. Raise [Not_found] if it is absent. *)

(** {5 ML tactic extensions} *)

type ml_tactic =
  typed_generic_argument list -> Geninterp.interp_sign -> unit Proofview.tactic
(** Type of external tactics, used by [TacExtend]. *)

val register_ml_tactic : ?overwrite:bool -> ml_tactic_name -> ml_tactic -> unit
(** Register an external tactic. *)

val interp_ml_tactic : ml_tactic_name -> ml_tactic
(** Get the named tactic. Raises a user error if it does not exist. *)
