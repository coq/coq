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

Ltac2 Type t := inductive.
(** An [inductive] is a name of a mutually inductive type and the index of an
    inductive block within that type. *)

Ltac2 @ external equal : t -> t -> bool := "rocq-runtime.plugins.ltac2" "ind_equal".
(** Equality test. *)

Ltac2 Type data.
(** The actual data specified by a concrete declaration of an inductive type,
    containing, e.g., its constructors and its parameters. A value of type
    [data] corresponds to one inductive type within a larger mutually inductive
    block. *)

Ltac2 @ external data : t -> data := "rocq-runtime.plugins.ltac2" "ind_data".
(** Get the value named by [t] in the current environment. Panics if [t] is not
    in scope. *)

Ltac2 @ external repr : data -> t := "rocq-runtime.plugins.ltac2" "ind_repr".
(** Returns the name of the inductive type corresponding to the block. Inverse
    of [data]. *)

Ltac2 @ external index : t -> int := "rocq-runtime.plugins.ltac2" "ind_index".
(** Returns the index of the inductive type inside its mutual block. Guaranteed
    to range between [0] and [nblocks data - 1] where [data] was retrieved using
    the above function. *)

Ltac2 @ external nblocks : data -> int := "rocq-runtime.plugins.ltac2" "ind_nblocks".
(** Returns the number of inductive types appearing in a mutual block. *)

Ltac2 @ external nconstructors : data -> int := "rocq-runtime.plugins.ltac2" "ind_nconstructors".
(** Returns the number of constructors appearing in the current block. *)

Ltac2 @ external get_block : data -> int -> data := "rocq-runtime.plugins.ltac2" "ind_get_block".
(** [get_block data n] is the block corresponding to the nth inductive type in
    [data]'s parent mutually inductive type. Index must range between [0] and
    [nblocks data - 1], otherwise the function panics. *)

Ltac2 @ external get_constructor : data -> int -> constructor := "rocq-runtime.plugins.ltac2" "ind_get_constructor".
(** Returns the nth constructor of the inductive type. Index must range between
    [0] and [nconstructors data - 1], otherwise the function panics. *)

Ltac2 @ external nparams : data -> int := "rocq-runtime.plugins.ltac2" "ind_get_nparams".
(** The number of parameters of the inductive type, including both uniform and
    non-uniform parameters. Does not count local let-ins. *)

Ltac2 @ external nparams_uniform : data -> int := "rocq-runtime.plugins.ltac2" "ind_get_nparams_rec".
(** The number of recursively uniform (i.e., ordinary) parameters of the
    inductive type. *)

Ltac2 @ external get_projections : data -> projection array option
  := "rocq-runtime.plugins.ltac2" "ind_get_projections".
(** Returns the list of projections for a primitive record, or [None] if the
    inductive is not a primitive record. *)

Ltac2 @ external constructor_nargs : data -> int array := "rocq-runtime.plugins.ltac2" "constructor_nargs".
(** [Array.get (constructor_nargs data) n] is the number of non-parameter
    arguments accepted by the [n]th constructor of this inductive type. Add
    [Array.get (constructor_nargs data) n] to [Ind.nparams_data] to get the total
    number of arguments of the constructor. *)

Ltac2 @ external constructor_ndecls : data -> int array := "rocq-runtime.plugins.ltac2" "constructor_ndecls".
(** [Array.get (constructor_ndecls data) n] is the number of variables bound in
    a pattern match expression by the [n]th constructor of this inductive type.
    Can be greater than [constructor_nargs] if the constructors have local
    let-bindings, e.g., applied to [Inductive Ind (A : Type) (f : A -> A) : Set
    := Constr (x : A) (y := f x)] it would return [[|2|]], because in [match t
    with Constr _ _ x y => e end], [x] and [y] are bound in [e]. *)
