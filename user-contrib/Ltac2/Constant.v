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

Ltac2 Type t := constant.

Ltac2 @ external equal : constant -> constant -> bool := "coq-core.plugins.ltac2" "constant_equal".
(** Constants obtained through module aliases or Include are not
    considered equal by this function. *)

(* "Set" is a keyword so call it FSet for Finite Set *)
Module FSet.
  Ltac2 Type elt := t.

  Ltac2 Type t.

  Ltac2 @ external empty : unit -> t := "coq-core.plugins.ltac2" "constant_set_empty".

  Ltac2 @ external is_empty : t -> bool := "coq-core.plugins.ltac2" "constant_set_is_empty".

  Ltac2 @ external mem : elt -> t -> bool := "coq-core.plugins.ltac2" "constant_set_mem".

  Ltac2 @ external add : elt -> t -> t := "coq-core.plugins.ltac2" "constant_set_add".

  Ltac2 @ external remove : elt -> t -> t := "coq-core.plugins.ltac2" "constant_set_remove".

  Ltac2 @ external union : t -> t -> t := "coq-core.plugins.ltac2" "constant_set_union".

  Ltac2 @ external inter : t -> t -> t := "coq-core.plugins.ltac2" "constant_set_inter".

  Ltac2 @ external diff : t -> t -> t := "coq-core.plugins.ltac2" "constant_set_diff".

  Ltac2 @ external equal : t -> t -> bool := "coq-core.plugins.ltac2" "constant_set_equal".

  Ltac2 @ external subset : t -> t -> bool := "coq-core.plugins.ltac2" "constant_set_subset".

  Ltac2 @ external cardinal : t -> int := "coq-core.plugins.ltac2" "constant_set_cardinal".

  Ltac2 @ external elements : t -> elt list := "coq-core.plugins.ltac2" "constant_set_elements".

End FSet.

Module Map.
  Ltac2 Type key := t.

  Ltac2 Type 'a t.

  Ltac2 @ external empty : unit -> 'a t := "coq-core.plugins.ltac2" "constant_map_empty".

  Ltac2 @ external is_empty : 'a t -> bool := "coq-core.plugins.ltac2" "constant_map_is_empty".

  Ltac2 @ external mem : key -> 'a t -> bool := "coq-core.plugins.ltac2" "constant_map_mem".

  Ltac2 @ external add : key -> 'a -> 'a t -> 'a t := "coq-core.plugins.ltac2" "constant_map_add".

  Ltac2 @ external remove : key -> 'a t -> 'a t := "coq-core.plugins.ltac2" "constant_map_remove".

  Ltac2 @ external find_opt : key -> 'a t -> 'a option := "coq-core.plugins.ltac2" "constant_map_find_opt".

  Ltac2 @ external mapi : (key -> 'a -> 'b) -> 'a t -> 'b t := "coq-core.plugins.ltac2" "constant_map_mapi".

  Ltac2 @ external fold : (key -> 'a -> 'acc) -> 'a t -> 'acc -> 'acc := "coq-core.plugins.ltac2" "constant_map_fold".

  Ltac2 @ external cardinal : 'a t -> int := "coq-core.plugins.ltac2" "constant_map_cardinal".

  Ltac2 @ external bindings : 'a t -> (key * 'a) list := "coq-core.plugins.ltac2" "constant_map_bindings".

  Ltac2 @ external domain : 'a t -> FSet.t := "coq-core.plugins.ltac2" "constant_map_domain".

End Map.
