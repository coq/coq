(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Compatibility file for making Coq act similar to Coq v8.13 *)

Require Export Coq.Compat.Coq814.

Require Coq.micromega.Lia.
Module Export Coq.
  Module Export omega.
    Module Export Omega.
      #[deprecated(since="8.12", note="The omega tactic was removed in v8.14.  You're now relying on the lia tactic.")]
      Ltac omega := Lia.lia.
    End Omega.
  End omega.
End Coq.
