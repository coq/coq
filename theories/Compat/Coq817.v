(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Compatibility file for making Coq act similar to Coq v8.17 *)

Local Set Warnings "-masking-absolute-name".

Require Export Coq.Compat.Coq818.

Require Coq.Lists.ListSet.

Module Export Coq.
  Module Export Lists.
    Module Export ListSet.
      Import List ListSet.
      Local Lemma Private_set_diff_nodup :
        forall (A:Type) (Aeq_dec : forall x y:A, {x = y} + {x <> y}) l l',
         NoDup l -> NoDup l' -> NoDup (set_diff Aeq_dec l l').
      Proof. auto using set_diff_nodup. Qed.
      #[deprecated(since="8.18", note="The NoDup assumption for the second list has been dropped, please adjust uses of the lemma")]
      Notation set_diff_nodup := Private_set_diff_nodup.
    End ListSet.
  End Lists.
End Coq.
