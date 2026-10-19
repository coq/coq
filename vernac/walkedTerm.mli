(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Terms keyed by what the traversal of {!Assumptions} reads of them. *)

(** Tables of terms. Two terms are one key when the traversal of
    {!Assumptions} reads the same references in the same structure: the
    comparison follows [Assumptions.fold_with_full_binders] arm by arm, with no
    application flattened and no cast looked through. A [Const], [Ind] or
    [Construct] is the same only when both its user name and its canonical name
    agree. It ignores only what the traversal never reads: binder names,
    universe instances, sorts, the kind of a cast, the strategy and relevance
    annotations and the binder contexts of a match, the name of a projection,
    and the recursion indices of a fixpoint. Keys hash by the fields it
    compares and no others, so equal keys hash equally. *)
module Tbl : Hashtbl.S with type key = Constr.t
