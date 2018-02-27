(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(** Custom notations and implicits for Coq prelude definitions.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

(** Haskell-style notations for the unit type and value. *)

Notation " () " := Datatypes.unit : type_scope.
Notation " () " := tt.

(** Set maximally inserted implicit arguments for standard definitions. *)

Arguments Some {A} _.
Arguments None {A}.

Arguments pair {A B} _ _.
Arguments fst {A B} _.
Arguments snd {A B} _.

Arguments nil {A}.
Arguments cons {A} _ _.

Require List.
Export List.ListNotations.

Require Import Bvector.
