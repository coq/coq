(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
Require Ltac2.FSet.

Module Free.

Ltac2 Type t := ident FSet.t.
(** Type of sets of free variables *)

Ltac2 union : t -> t -> t := FSet.union.

Ltac2 of_ids (x:ident list) : t :=
  List.fold_left (fun acc x => FSet.add x acc) x (FSet.empty FSet.Tags.ident_tag).

Ltac2 @ external of_constr : constr -> t := "coq-core.plugins.ltac2" "fresh_free_of_constr".

Ltac2 of_goal () := of_ids (List.map (fun (id, _, _) => id) (Control.hyps ())).

End Free.

Ltac2 @ external fresh : Free.t -> ident -> ident := "coq-core.plugins.ltac2" "fresh_fresh".
(** Generate a fresh identifier with the given base name which is not a
    member of the provided set of free variables. *)

Ltac2 in_goal id := Fresh.fresh (Free.of_goal ()) id.
