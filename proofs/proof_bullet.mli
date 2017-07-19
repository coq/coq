(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(**********************************************************)
(*                                                        *)
(*                                 Bullets                *)
(*                                                        *)
(**********************************************************)

open Proof

type t = Vernacexpr.bullet

(** A [behavior] is the data of a put function which
    is called when a bullet prefixes a tactic, a suggest function
    suggesting the right bullet to use on a given proof, together
    with a name to identify the behavior. *)
type behavior = {
  name : string;
  put : proof -> t -> proof;
  suggest: proof -> Pp.t
}

(** A registered behavior can then be accessed in Coq
    through the command [Set Bullet Behavior "name"].

    Two modes are registered originally:
    * "Strict Subproofs":
      - If this bullet follows another one of its kind, defocuses then focuses
        (which fails if the focused subproof is not complete).
      - If it is the first bullet of its kind, then focuses a new subproof.
    * "None": bullets don't do anything *)
val register_behavior : behavior -> unit

(** Handles focusing/defocusing with bullets:
     *)
val put : proof -> t -> proof
val suggest : proof -> Pp.t

(**********************************************************)
(*                                                        *)
(*                     Default goal selector              *)
(*                                                        *)
(**********************************************************)

val pr_goal_selector : Vernacexpr.goal_selector -> Pp.std_ppcmds
val get_default_goal_selector : unit -> Vernacexpr.goal_selector

