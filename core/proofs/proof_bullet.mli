(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**********************************************************)
(*                                                        *)
(*                                 Bullets                *)
(*                                                        *)
(**********************************************************)

type t =
    | Dash of int
    | Star of int
    | Plus of int

(** A [behavior] is the data of a put function which
    is called when a bullet prefixes a tactic, a suggest function
    suggesting the right bullet to use on a given proof, together
    with a name to identify the behavior. *)
type behavior = {
  name : string;
  put : Proof.t -> t -> Proof.t;
  suggest: Proof.t -> Pp.t
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
val put : Proof.t -> t -> Proof.t
val suggest : Proof.t -> Pp.t
