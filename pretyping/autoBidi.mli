(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** [auto_bidy env sigma hj ~nargs tycon] produces a list [candargs]
   such that if [hj] applied to [nargs] has type [tycon] then the
   arguments must unify with the corresponding [candargs] (with [None]
   meaning no constraint).

    The list is produced by unifying without reduction, if no match
   can be confirmed it is empty.

    Will also return the empty list if the automatic bidirectionality
   option is unset. *)
val auto_bidi : Environ.env
  -> Evd.evar_map
  -> EConstr.unsafe_judgment
  -> nargs:int
  -> EConstr.types
  -> (Reduction.conv_pb * EConstr.t) option list
