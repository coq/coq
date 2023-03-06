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

Ltac2 Type t := int.

Ltac2 @ external equal : int -> int -> bool := "coq-core.plugins.ltac2" "int_equal".
Ltac2 @ external compare : int -> int -> int := "coq-core.plugins.ltac2" "int_compare".
Ltac2 @ external add : int -> int -> int := "coq-core.plugins.ltac2" "int_add".
Ltac2 @ external sub : int -> int -> int := "coq-core.plugins.ltac2" "int_sub".
Ltac2 @ external mul : int -> int -> int := "coq-core.plugins.ltac2" "int_mul".

(* Note: unlike Coq Z division, Ltac2 matches OCaml division and rounds towards 0, so 1/-2 = 0 *)
Ltac2 @ external div : int -> int -> int := "coq-core.plugins.ltac2" "int_div".

Ltac2 @ external mod : int -> int -> int := "coq-core.plugins.ltac2" "int_mod".
Ltac2 @ external neg : int -> int := "coq-core.plugins.ltac2" "int_neg".
Ltac2 @ external abs : int -> int := "coq-core.plugins.ltac2" "int_abs".

Ltac2 @ external asr : int -> int -> int := "coq-core.plugins.ltac2" "int_asr".
Ltac2 @ external lsl : int -> int -> int := "coq-core.plugins.ltac2" "int_lsl".
Ltac2 @ external lsr : int -> int -> int := "coq-core.plugins.ltac2" "int_lsr".
Ltac2 @ external land : int -> int -> int := "coq-core.plugins.ltac2" "int_land".
Ltac2 @ external lor : int -> int -> int := "coq-core.plugins.ltac2" "int_lor".
Ltac2 @ external lxor : int -> int -> int := "coq-core.plugins.ltac2" "int_lxor".
Ltac2 @ external lnot : int -> int := "coq-core.plugins.ltac2" "int_lnot".

Ltac2 lt (x : int) (y : int) := equal (compare x y) -1.
Ltac2 gt (x : int) (y : int) := equal (compare x y) 1.
Ltac2 le (x : int) (y : int) :=
  (* we might use [lt x (add y 1)], but that has the wrong behavior on MAX_INT *)
  match equal x y with
  | true => true
  | false => lt x y
  end.
Ltac2 ge (x : int) (y : int) :=
  (* we might use [lt (add x 1) y], but that has the wrong behavior on MAX_INT *)
  match equal x y with
  | true => true
  | false => gt x y
  end.

(* "Set" is a keyword so call it FSet for Finite Set *)
Module FSet.
  Ltac2 Type elt := t.

  Ltac2 Type t.

  Ltac2 @ external empty : unit -> t := "coq-core.plugins.ltac2" "int_set_empty".

  Ltac2 @ external is_empty : t -> bool := "coq-core.plugins.ltac2" "int_set_is_empty".

  Ltac2 @ external mem : elt -> t -> bool := "coq-core.plugins.ltac2" "int_set_mem".

  Ltac2 @ external add : elt -> t -> t := "coq-core.plugins.ltac2" "int_set_add".

  Ltac2 @ external remove : elt -> t -> t := "coq-core.plugins.ltac2" "int_set_remove".

  Ltac2 @ external union : t -> t -> t := "coq-core.plugins.ltac2" "int_set_union".

  Ltac2 @ external inter : t -> t -> t := "coq-core.plugins.ltac2" "int_set_inter".

  Ltac2 @ external diff : t -> t -> t := "coq-core.plugins.ltac2" "int_set_diff".

  Ltac2 @ external equal : t -> t -> bool := "coq-core.plugins.ltac2" "int_set_equal".

  Ltac2 @ external subset : t -> t -> bool := "coq-core.plugins.ltac2" "int_set_subset".

  Ltac2 @ external cardinal : t -> int := "coq-core.plugins.ltac2" "int_set_cardinal".

  Ltac2 @ external elements : t -> elt list := "coq-core.plugins.ltac2" "int_set_elements".

End FSet.

Module Map.
  Ltac2 Type key := t.

  Ltac2 Type 'a t.

  Ltac2 @ external empty : unit -> 'a t := "coq-core.plugins.ltac2" "int_map_empty".

  Ltac2 @ external is_empty : 'a t -> bool := "coq-core.plugins.ltac2" "int_map_is_empty".

  Ltac2 @ external mem : key -> 'a t -> bool := "coq-core.plugins.ltac2" "int_map_mem".

  Ltac2 @ external add : key -> 'a -> 'a t -> 'a t := "coq-core.plugins.ltac2" "int_map_add".

  Ltac2 @ external remove : key -> 'a t -> 'a t := "coq-core.plugins.ltac2" "int_map_remove".

  Ltac2 @ external find_opt : key -> 'a t -> 'a option := "coq-core.plugins.ltac2" "int_map_find_opt".

  Ltac2 @ external mapi : (key -> 'a -> 'b) -> 'a t -> 'b t := "coq-core.plugins.ltac2" "int_map_mapi".

  Ltac2 @ external fold : (key -> 'a -> 'acc) -> 'a t -> 'acc -> 'acc := "coq-core.plugins.ltac2" "int_map_fold".

  Ltac2 @ external cardinal : 'a t -> int := "coq-core.plugins.ltac2" "int_map_cardinal".

  Ltac2 @ external bindings : 'a t -> (key * 'a) list := "coq-core.plugins.ltac2" "int_map_bindings".

  Ltac2 @ external domain : 'a t -> FSet.t := "coq-core.plugins.ltac2" "int_map_domain".

End Map.
