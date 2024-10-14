(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Delta implies all consts (both global (= by [kernel_name]) and local
    (= by [Rel] or [Var])), all evars, and letin's. Rem: reduction of a
    Rel/Var bound to a term is Delta, but reduction of a LetIn expression
    is Letin reduction *)

(** Set of reduction kinds. *)
type reds

(** Reduction kind. *)
type red_kind

val fBETA : red_kind
val fDELTA : red_kind
val fMATCH : red_kind
val fFIX : red_kind
val fCOFIX : red_kind
val fZETA : red_kind
val fCONST : Names.Constant.t -> red_kind
val fPROJ : Names.Projection.Repr.t -> red_kind
val fVAR : Names.Id.t -> red_kind

(** No reduction at all *)
val no_red : reds

(** Adds a reduction kind to a set *)
val red_add : reds -> red_kind -> reds

(** Removes a reduction kind from a set *)
val red_sub : reds -> red_kind -> reds

(** Adds a list of reduction kind to a set *)
val red_add_list : reds -> red_kind list -> reds

(** Removes a list of reduction kind from a set *)
val red_sub_list : reds -> red_kind list -> reds

(** Adds a reduction kind to a set *)
val red_add_transparent : reds -> TransparentState.t -> reds

(** Retrieve the transparent state of the reduction flags *)
val red_transparent : reds -> TransparentState.t

(** Build a reduction set from scratch = iter [red_add] on [no_red] *)
val mkflags : red_kind list -> reds

(** Tests if a reduction kind is set *)
val red_set : reds -> red_kind -> bool

(** This tests if the projection is in unfolded state already or is unfodable
    due to delta. *)
val red_projection : reds -> Names.Projection.t -> bool

(* These flags do not contain eta *)
val all : reds
val allnolet : reds
val beta : reds
val betadeltazeta : reds
val betaiota : reds
val betaiotazeta : reds
val betazeta : reds
val delta : reds
val zeta : reds
val nored : reds
