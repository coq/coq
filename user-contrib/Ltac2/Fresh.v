(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.
Require Ltac2.Control.
Require Ltac2.List.

Module Free.

Ltac2 Type t.
(** Type of sets of free variables *)

Ltac2 @external empty : t := "rocq-runtime.plugins.ltac2" "fresh_free_empty".

Ltac2 @external add : ident -> t -> t := "rocq-runtime.plugins.ltac2" "fresh_free_add".

Ltac2 @external union : t -> t -> t := "rocq-runtime.plugins.ltac2" "fresh_free_union".

Ltac2 @external of_ids : ident list -> t := "rocq-runtime.plugins.ltac2" "fresh_free_of_ids".

Ltac2 @external of_constr : constr -> t := "rocq-runtime.plugins.ltac2" "fresh_free_of_constr".

Ltac2 of_goal () := of_ids (List.map (fun (id, _, _) => id) (Control.hyps ())).

End Free.

(** Generate a fresh identifier with the given base name which is not a
    member of the provided set of free variables, and update the set.
    More efficient than composing [fresh] and [Free.add]. *)
Ltac2 @external next : Free.t -> ident -> ident * Free.t := "rocq-runtime.plugins.ltac2" "fresh_next".

(** Generate a fresh identifier with the given base name which is not a
    member of the provided set of free variables. *)
Ltac2 @external fresh : Free.t -> ident -> ident := "rocq-runtime.plugins.ltac2" "fresh_fresh".

Ltac2 in_goal id := Fresh.fresh (Free.of_goal ()) id.
