(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**** Tactics Tauto and Intuition ****)

(**** Tauto:
  Tactic for automating proof in Intuionnistic Propositional Calculus, based on
  the contraction-free LJT* of Dickhoff ****)

(**** Intuition:
  Simplifications of goals, based on LJT* calcul ****)

(**** Examples of intuitionistic tautologies ****)
Parameter A B C D E F : Prop.
Parameter even : nat -> Prop.
Parameter P : nat -> Prop.

Lemma Ex_Wallen : (A -> B /\ C) -> (A -> B) \/ (A -> C).
Proof.
   tauto.
Qed.

Lemma Ex_Klenne : ~ ~ (A \/ ~ A).
Proof.
   tauto.
Qed.

Lemma Ex_Klenne' : forall n : nat, ~ ~ (even n \/ ~ even n).
Proof.
   tauto.
Qed.

Lemma Ex_Klenne'' :
 ~ ~ ((forall n : nat, even n) \/ ~ (forall m : nat, even m)).
Proof.
   tauto.
Qed.

Lemma tauto : (forall x : nat, P x) -> forall y : nat, P y.
Proof.
   tauto.
Qed.

Lemma tauto1 : A -> A.
Proof.
   tauto.
Qed.

Lemma tauto2 : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
   tauto.
Qed.

Lemma a : forall (x0 : A \/ B) (x1 : B /\ C), A -> B.
Proof.
   tauto.
Qed.

Lemma a2 : (A -> B /\ C) -> (A -> B) \/ (A -> C).
Proof.
   tauto.
Qed.

Lemma a4 : ~ A -> ~ A.
Proof.
   tauto.
Qed.

Lemma e2 : ~ ~ (A \/ ~ A).
Proof.
   tauto.
Qed.

Lemma e4 : ~ ~ (A \/ B -> A \/ B).
Proof.
   tauto.
Qed.

Lemma y0 :
 forall (x0 : A) (x1 : ~ A) (x2 : A -> B) (x3 : A \/ B) (x4 : A /\ B),
 A -> False.
Proof.
   tauto.
Qed.

Lemma y1 : forall x0 : (A /\ B) /\ C, B.
Proof.
   tauto.
Qed.

Lemma y2 : forall (x0 : A) (x1 : B), C \/ B.
Proof.
   tauto.
Qed.

Lemma y3 : forall x0 : A /\ B, B /\ A.
Proof.
   tauto.
Qed.

Lemma y5 : forall x0 : A \/ B, B \/ A.
Proof.
   tauto.
Qed.

Lemma y6 : forall (x0 : A -> B) (x1 : A), B.
Proof.
   tauto.
Qed.

Lemma y7 : forall (x0 : A /\ B -> C) (x1 : B) (x2 : A), C.
Proof.
   tauto.
Qed.

Lemma y8 : forall (x0 : A \/ B -> C) (x1 : A), C.
Proof.
   tauto.
Qed.

Lemma y9 : forall (x0 : A \/ B -> C) (x1 : B), C.
Proof.
   tauto.
Qed.

Lemma y10 : forall (x0 : (A -> B) -> C) (x1 : B), C.
Proof.
   tauto.
Qed.

(* This example took much time with the old version of Tauto *)
Lemma critical_example0 : (~ ~ B -> B) -> (A -> B) -> ~ ~ A -> B.
Proof.
   tauto.
Qed.

(* Same remark as previously *)
Lemma critical_example1 : (~ ~ B -> B) -> (~ B -> ~ A) -> ~ ~ A -> B.
Proof.
   tauto.
Qed.

(* This example took very much time (about 3mn on a PIII 450MHz in bytecode)
   with the old Tauto. Now, it's immediate (less than 1s). *)
Lemma critical_example2 : (~ A <-> B) -> (~ B <-> A) -> (~ ~ A <-> A).
Proof.
   tauto.
Qed.

(* This example was a bug *)
Lemma old_bug0 :
 (~ A <-> B) -> (~ (C \/ E) <-> D /\ F) -> (~ (C \/ A \/ E) <-> D /\ B /\ F).
Proof.
   tauto.
Qed.

(* Another bug *)
Lemma old_bug1 : ((A -> B -> False) -> False) -> (B -> False) -> False.
Proof.
   tauto.
Qed.

(* A bug again *)
Lemma old_bug2 :
 ((((C -> False) -> A) -> ((B -> False) -> A) -> False) -> False) ->
 (((C -> B -> False) -> False) -> False) -> ~ A -> A.
Proof.
   tauto.
Qed.

(* A bug from CNF form *)
Lemma old_bug3 :
 ((~ A \/ B) /\ (~ B \/ B) /\ (~ A \/ ~ B) /\ (~ B \/ ~ B) -> False) ->
 ~ ((A -> B) -> B) -> False.
Proof.
   tauto.
Qed.

(* sometimes, the behaviour of Tauto depends on the order of the hyps *)
Lemma old_bug3bis :
 ~ ((A -> B) -> B) ->
 ((~ B \/ ~ B) /\ (~ B \/ ~ A) /\ (B \/ ~ B) /\ (B \/ ~ A) -> False) -> False.
Proof.
   tauto.
Qed.

(* A bug found by Freek Wiedijk <freek@cs.kun.nl> *)
Lemma new_bug :
 ((A <-> B) -> (B <-> C)) ->
 ((B <-> C) -> (C <-> A)) -> ((C <-> A) -> (A <-> B)) -> (A <-> B).
Proof.
   tauto.
Qed.


(*  A private club has the following rules :
 *
 *  . rule 1 : Every non-scottish member wears red socks
 *  . rule 2 : Every member wears a kilt or doesn't wear red socks
 *  . rule 3 : The married members don't go out on sunday
 *  . rule 4 : A member goes out on sunday if and only if he is scottish
 *  . rule 5 : Every member who wears a kilt is scottish and married
 *  . rule 6 : Every scottish member wears a kilt
 *
 *  Actually, no one can be accepted !
 *)

Section club.

Variable Scottish RedSocks WearKilt Married GoOutSunday : Prop.

Hypothesis rule1 : ~ Scottish -> RedSocks.
Hypothesis rule2 : WearKilt \/ ~ RedSocks.
Hypothesis rule3 : Married -> ~ GoOutSunday.
Hypothesis rule4 : GoOutSunday <-> Scottish.
Hypothesis rule5 : WearKilt -> Scottish /\ Married.
Hypothesis rule6 : Scottish -> WearKilt.

Lemma NoMember : False.
 tauto.
Qed.

End club.

(**** Use of Intuition ****)
Lemma intu0 :
 (forall x : nat, P x) /\ B -> (forall y : nat, P y) /\ P 0 \/ B /\ P 0.
Proof.
   intuition.
Qed.

Lemma intu1 :
 (forall A : Prop, A \/ ~ A) -> forall x y : nat, x = y \/ x <> y.
Proof.
   intuition.
Qed.

