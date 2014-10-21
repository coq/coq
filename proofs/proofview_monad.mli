(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file defines the datatypes used as internal states by the
    tactic monad, and specialises the [Logic_monad] to these type. *)

(** {6 State types} *)

(** Type of proof views: current [evar_map] together with the list of
    focused goals. *)
type proofview = { solution : Evd.evar_map; comb : Goal.goal list }


(** {6 Instantiation of the logic monad} *)

module P : sig
  type s = proofview * Environ.env

  (** Status (safe/unsafe) * shelved goals * given up *)
  type w = bool * Evar.t list * Evar.t list

  val wunit : w
  val wprod : w -> w -> w

  type e = unit
end

module Logical : module type of Logic_monad.Logical(P)


(** {6 Lenses to access to components of the states} *)

module type State = sig
  type t
  val get : t Logical.t
  val set : t -> unit Logical.t
  val modify : (t->t) -> unit Logical.t
end

module type Writer = sig
  type t
  val put : t -> unit Logical.t
end

(** Lens to the [proofview]. *)
module Pv : State with type t := proofview

(** Lens to the [evar_map] of the proofview. *)
module Solution : State with type t := Evd.evar_map

(** Lens to the list of focused goals. *)
module Comb : State with type t = Evar.t list

(** Lens to the global environment. *)
module Env : State with type t := Environ.env

(** Lens to the tactic status ([true] if safe, [false] if unsafe) *)
module Status : Writer with type t := bool

(** Lens to the list of goals which have been shelved during the
    execution of the tactic. *)
module Shelf : Writer with type t = Evar.t list

(** Lens to the list of goals which were given up during the execution
    of the tactic. *)
module Giveup : Writer with type t = Evar.t list
