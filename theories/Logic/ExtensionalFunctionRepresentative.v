(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module states a limited form axiom of functional
    extensionality which selects a canonical representative in each
    class of extensional functions *)

(** Its main interest is that it is the needed ingredient to provide
    axiom of choice on setoids (a.k.a. axiom of extensional choice)
    when combined with classical logic and axiom of (intensonal)
    choice *)

(** It provides extensionality of functions while still supporting (a
    priori) an intensional interpretation of equality *)

Axiom extensional_function_representative :
  forall A B, exists repr, forall (f : A -> B),
  (forall x, f x = repr f x) /\
  (forall g, (forall x, f x = g x) -> repr f = repr g).
