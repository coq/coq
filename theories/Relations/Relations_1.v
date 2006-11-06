(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(****************************************************************************)
(*                                                                          *)
(*                         Naive Set Theory in Coq                          *)
(*                                                                          *)
(*                     INRIA                        INRIA                   *)
(*              Rocquencourt                        Sophia-Antipolis        *)
(*                                                                          *)
(*                                 Coq V6.1                                 *)
(*									    *)
(*			         Gilles Kahn 				    *)
(*				 Gerard Huet				    *)
(*									    *)
(*									    *)
(*                                                                          *)
(* Acknowledgments: This work was started in July 1993 by F. Prost. Thanks  *)
(* to the Newton Institute for providing an exceptional work environment    *)
(* in Summer 1995. Several developments by E. Ledinot were an inspiration.  *)
(****************************************************************************)

(*i $Id$ i*)

Require Export Relation_Definitions.

Set Implicit Arguments.

Definition contains U (R R':relation U) := forall x y:U, R' x y -> R x y.

Hint Unfold contains.

(* Compatibility *)

Notation Relation := relation (only parsing).
Notation Reflexive := reflexive (only parsing).
Notation Symmetric := symmetric (only parsing).
Notation Transitive := transitive (only parsing).
Notation Antisymmetric := antisymmetric (only parsing).
Notation same_relation := (@same_relation _).
Notation Preorder := preorder (only parsing).
Notation Definition_of_preorder := Build_preorder (only parsing).
Notation Order := order (only parsing).
Notation Definition_of_order := Build_order (only parsing).
Notation Equivalence := equivalence (only parsing).
Notation Definition_of_equivalence := Build_equivalence (only parsing).
Notation PER := PER.
Notation Definition_of_PER := Build_PER (only parsing).

(* Compatibility notes

  [same_relation] was defined on endorelations as a pair of [contains], now
  it is defined on arbitrary relations and on [inclusion], resulting in a
  reverse order in the two conjuncts!

*)
