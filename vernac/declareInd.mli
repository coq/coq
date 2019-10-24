(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Registering a mutual inductive definition together with its
   associated schemes *)

type one_inductive_impls =
  Impargs.manual_implicits (* for inds *) *
  Impargs.manual_implicits list (* for constrs *)

val declare_mutual_inductive_with_eliminations
  : ?primitive_expected:bool
  -> Entries.mutual_inductive_entry
  -> UnivNames.universe_binders
  -> one_inductive_impls list
  -> Names.MutInd.t
