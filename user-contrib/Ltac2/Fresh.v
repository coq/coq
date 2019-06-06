(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.

Module Free.

Ltac2 Type t.
(** Type of sets of free variables *)

Ltac2 @ external union : t -> t -> t := "ltac2" "fresh_free_union".

Ltac2 @ external of_ids : ident list -> t := "ltac2" "fresh_free_of_ids".

Ltac2 @ external of_constr : constr -> t := "ltac2" "fresh_free_of_constr".

End Free.

Ltac2 @ external fresh : Free.t -> ident -> ident := "ltac2" "fresh_fresh".
(** Generate a fresh identifier with the given base name which is not a
    member of the provided set of free variables. *)
