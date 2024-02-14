(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* File Eqdep.v created by Christine Paulin-Mohring in Coq V5.6, May 1992 *)
(* Abstraction with respect to the eq_rect_eq axiom and creation of
   EqdepFacts.v by Hugo Herbelin, Mar 2006 *)

(** This file axiomatizes the invariance by substitution of reflexive
    equality proofs [[Streicher93]] and exports its consequences, such
    as the injectivity of the projection of the dependent pair.

    [[Streicher93]] T. Streicher, Semantical Investigations into
    Intensional Type Theory, Habilitationsschrift, LMU München, 1993.
*)

Require Export EqdepFacts.
Import EqNotations.

Module Eq_rect_eq.

Axiom eq_rect_eq :
  forall (A:Type) (x:A) (P:A -> Type) (p:P x) (e:x = x), p = rew [P] e in p.

End Eq_rect_eq.

Module EqdepTheory := EqdepTheory(Eq_rect_eq).
Export EqdepTheory.

(** Exported hints *)

#[global]
Hint Resolve eq_dep_eq: eqdep.
#[global]
Hint Resolve inj_pair2 inj_pairT2: eqdep.
