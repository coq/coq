(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module defines potentially focussing tactics. They are used by Ltac to
    emulate the historical behaviour of always-focussed tactics while still
    allowing to remain global when the goal is not needed. *)

type +'a focus

type +'a t = 'a focus Proofview.tactic
(** The type of focussing tactics. A focussing tactic is like a normal tactic,
    except that it is able to remember it have entered a goal. Whenever this is
    the case, each subsequent effect of the tactic is dispatched on the
    focussed goals. This is a monad. *)

(** {5 Monadic interface} *)

val return : 'a -> 'a t
(** The unit of the monad. *)

val bind : 'a t -> ('a -> 'b t) -> 'b t
(** The bind of the monad. *)

(** {5 Operations} *)

val lift : 'a Proofview.tactic -> 'a t
(** Transform a tactic into a focussing tactic. The resulting tactic is not
    focussed. *)

val run : 'a t -> ('a -> unit Proofview.tactic) -> unit Proofview.tactic
(** Given a continuation producing a tactic, evaluates the focussing tactic. If
    the tactic has not focussed, then the continuation is evaluated once.
    Otherwise it is called in each of the currently focussed goals. *)

(** {5 Focussing} *)

val nf_enter : (Proofview.Goal.t -> 'a t) -> 'a t
(** Enter a goal. The resulting tactic is focussed. *)

val enter : (Proofview.Goal.t -> 'a t) -> 'a t
(** Enter a goal, without evar normalization. The resulting tactic is
    focussed. *)

val with_env : 'a t -> (Environ.env*'a) t
(** [with_env t] returns, in addition to the return type of [t], an
    environment, which is the global environment if [t] does not focus on
    goals, or the local goal environment if [t] focuses on goals. *)

(** {5 Notations} *)

val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
(** Notation for {!bind}. *)

val (<*>) : unit t -> 'a t -> 'a t
(** Sequence. *)

(** {5 List operations} *)

module List : Monad.ListS with type 'a t := 'a t

(** {5 Notations} *)

module Notations :
sig
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
  val (<*>) : unit t -> 'a t -> 'a t
end
