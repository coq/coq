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
From Ltac2 Require FSet.

Import FSet.Tags.

Ltac2 Type ('k, 'v) t.

Ltac2 @ external empty : 'k tag -> ('k, 'v) t := "rocq-runtime.plugins.ltac2" "fmap_empty".

Ltac2 @ external is_empty : ('k, 'v) t -> bool := "rocq-runtime.plugins.ltac2" "fmap_is_empty".

Ltac2 @ external mem : 'k -> ('k, 'v) t -> bool := "rocq-runtime.plugins.ltac2" "fmap_mem".

Ltac2 @ external add : 'k -> 'v -> ('k, 'v) t -> ('k, 'v) t := "rocq-runtime.plugins.ltac2" "fmap_add".

Ltac2 @ external remove : 'k -> ('k, 'v) t -> ('k, 'v) t := "rocq-runtime.plugins.ltac2" "fmap_remove".

Ltac2 @ external find_opt : 'k -> ('k, 'v) t -> 'v option := "rocq-runtime.plugins.ltac2" "fmap_find_opt".

Ltac2 @ external mapi : ('k -> 'v -> 'r) -> ('k, 'v) t -> ('k, 'r) t := "rocq-runtime.plugins.ltac2" "fmap_mapi".

Ltac2 @ external fold : ('k -> 'v -> 'acc -> 'acc) -> ('k, 'v) t -> 'acc -> 'acc := "rocq-runtime.plugins.ltac2" "fmap_fold".

Ltac2 @ external cardinal : ('k, 'v) t -> int := "rocq-runtime.plugins.ltac2" "fmap_cardinal".

Ltac2 @ external bindings : ('k, 'v) t -> ('k * 'v) list := "rocq-runtime.plugins.ltac2" "fmap_bindings".

Ltac2 @ external domain : ('k, 'v) t -> 'k FSet.t := "rocq-runtime.plugins.ltac2" "fmap_domain".
