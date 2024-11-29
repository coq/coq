(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Ltac2 Require Import Init.

Module Import Tags.
  Ltac2 Type 'a tag.

  Ltac2 @ external ident_tag : ident tag := "rocq-runtime.plugins.ltac2" "fmap_ident_tag".
  Ltac2 @ external int_tag : int tag := "rocq-runtime.plugins.ltac2" "fmap_int_tag".
  Ltac2 @ external inductive_tag : inductive tag := "rocq-runtime.plugins.ltac2" "fmap_inductive_tag".
  Ltac2 @ external constructor_tag : constructor tag := "rocq-runtime.plugins.ltac2" "fmap_constructor_tag".
  Ltac2 @ external constant_tag : constant tag := "rocq-runtime.plugins.ltac2" "fmap_constant_tag".

  (* NB: strings are copied when keys are added and read to prevent mutation *)
  Ltac2 @ external string_tag : string tag := "rocq-runtime.plugins.ltac2" "fmap_string_tag".
End Tags.

Ltac2 Type 'a t.

Ltac2 @ external empty : 'a tag -> 'a t := "rocq-runtime.plugins.ltac2" "fset_empty".

Ltac2 @ external is_empty : 'a t -> bool := "rocq-runtime.plugins.ltac2" "fset_is_empty".

Ltac2 @ external mem : 'a -> 'a t -> bool := "rocq-runtime.plugins.ltac2" "fset_mem".

Ltac2 @ external add : 'a -> 'a t -> 'a t := "rocq-runtime.plugins.ltac2" "fset_add".

Ltac2 @ external remove : 'a -> 'a t -> 'a t := "rocq-runtime.plugins.ltac2" "fset_remove".

Ltac2 @ external union : 'a t -> 'a t -> 'a t := "rocq-runtime.plugins.ltac2" "fset_union".

Ltac2 @ external inter : 'a t -> 'a t -> 'a t := "rocq-runtime.plugins.ltac2" "fset_inter".

Ltac2 @ external diff : 'a t -> 'a t -> 'a t := "rocq-runtime.plugins.ltac2" "fset_diff".

Ltac2 @ external equal : 'a t -> 'a t -> bool := "rocq-runtime.plugins.ltac2" "fset_equal".

Ltac2 @ external subset : 'a t -> 'a t -> bool := "rocq-runtime.plugins.ltac2" "fset_subset".

Ltac2 @ external cardinal : 'a t -> int := "rocq-runtime.plugins.ltac2" "fset_cardinal".

Ltac2 @ external elements : 'a t -> 'a list := "rocq-runtime.plugins.ltac2" "fset_elements".
