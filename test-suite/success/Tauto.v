(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(**** Tactics Tauto and Intuition ****)

(**** Tauto:
  Tactic for automating proof in Intuionnistic Propositional Calculus, based on
  the contraction-free LJT* of Dickhoff ****)

(**** Intuition:
  Simplifications of goals, based on LJT* calcul ****)

(**** Examples of intuitionistic tautologies ****)
Parameter A,B,C,D,E,F:Prop.
Parameter even:nat -> Prop.
Parameter P:nat -> Prop.

Lemma Ex_Wallen:(A->(B/\C)) -> ((A->B)\/(A->C)).
Proof.
  Tauto.
Save.

Lemma Ex_Klenne:~(~(A \/ ~A)).
Proof.
  Tauto.
Save.

Lemma Ex_Klenne':(n:nat)(~(~((even n) \/ ~(even n)))).
Proof.
  Tauto.
Save.

Lemma Ex_Klenne'':~(~(((n:nat)(even n)) \/ ~((m:nat)(even m)))).
Proof.
  Tauto.
Save.

Lemma tauto:((x:nat)(P x)) -> ((y:nat)(P y)).
Proof.
  Tauto.
Save.

Lemma tauto1:(A -> A).
Proof.
  Tauto.
Save.

Lemma tauto2:(A -> B -> C) -> (A -> B) -> A -> C.
Proof.
  Tauto.
Save.

Lemma a:(x0: (A \/ B))(x1:(B /\ C))(A -> B).
Proof.
  Tauto.
Save.

Lemma a2:((A -> (B /\ C)) -> ((A -> B) \/ (A -> C))).
Proof.
  Tauto.
Save.

Lemma a4:(~A -> ~A).
Proof.
  Tauto.
Save.

Lemma e2:~(~(A \/ ~A)).
Proof.
  Tauto.
Save.

Lemma e4:~(~((A \/ B) -> (A \/ B))).
Proof.
  Tauto.
Save.

Lemma y0:(x0:A)(x1: ~A)(x2:(A -> B))(x3:(A \/ B))(x4:(A /\ B))(A -> False).
Proof.
  Tauto.
Save.

Lemma y1:(x0:((A /\ B) /\ C))B.
Proof.
  Tauto.
Save.

Lemma y2:(x0:A)(x1:B)(C \/ B).
Proof.
  Tauto.
Save.

Lemma y3:(x0:(A /\ B))(B /\ A).
Proof.
  Tauto.
Save.

Lemma y5:(x0:(A \/ B))(B \/ A).
Proof.
  Tauto.
Save.

Lemma y6:(x0:(A -> B))(x1:A) B.
Proof.
  Tauto.
Save.

Lemma y7:(x0 : ((A /\ B) -> C))(x1 : B)(x2 : A) C.
Proof.
  Tauto.
Save.

Lemma y8:(x0 : ((A \/ B) -> C))(x1 : A) C.
Proof.
  Tauto.
Save.

Lemma y9:(x0 : ((A \/ B) -> C))(x1 : B) C.
Proof.
  Tauto.
Save.

Lemma y10:(x0 : ((A -> B) -> C))(x1 : B) C.
Proof.
  Tauto.
Save.

(* This example took much time with the old version of Tauto *)
Lemma critical_example0:(~~B->B)->(A->B)->~~A->B.
Proof.
  Tauto.
Save.

(* Same remark as previously *)
Lemma critical_example1:(~~B->B)->(~B->~A)->~~A->B.
Proof.
  Tauto.
Save.

(* This example took very much time (about 3mn on a PIII 450MHz in bytecode)
   with the old Tauto. Now, it's immediate (less than 1s). *)
Lemma critical_example2:(~A<->B)->(~B<->A)->(~~A<->A).
Proof.
  Tauto.
Save.

(* This example was a bug *)
Lemma old_bug0:(~A<->B)->(~(C\/E)<->D/\F)->~(C\/A\/E)<->D/\B/\F.
Proof.
  Tauto.
Save.

(* Another bug *)
Lemma old_bug1:((A->B->False)->False) -> (B->False) -> False.
Proof.
  Tauto.
Save.

(* A bug again *)
Lemma old_bug2:
  ((((C->False)->A)->((B->False)->A)->False)->False) ->
  (((C->B->False)->False)->False) ->
  ~A->A.
Proof.
  Tauto.
Save.

(* A bug from CNF form *)
Lemma old_bug3:
  ((~A\/B)/\(~B\/B)/\(~A\/~B)/\(~B\/~B)->False)->~((A->B)->B)->False.
Proof.
  Tauto.
Save.

(* sometimes, the behaviour of Tauto depends on the order of the hyps *)
Lemma old_bug3bis:
  ~((A->B)->B)->((~B\/~B)/\(~B\/~A)/\(B\/~B)/\(B\/~A)->False)->False.
Proof.
  Tauto.
Save.

(* A bug found by Freek Wiedijk <freek@cs.kun.nl> *)
Lemma new_bug:
 ((A<->B)->(B<->C)) ->
 ((B<->C)->(C<->A)) ->
 ((C<->A)->(A<->B)) ->
 (A<->B).
Proof.
  Tauto.
Save.


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

Variable Scottish, RedSocks, WearKilt, Married, GoOutSunday : Prop.

Hypothesis rule1 : ~Scottish -> RedSocks.
Hypothesis rule2 : WearKilt \/ ~RedSocks.
Hypothesis rule3 : Married -> ~GoOutSunday.
Hypothesis rule4 : GoOutSunday <-> Scottish.
Hypothesis rule5 : WearKilt -> (Scottish /\ Married).
Hypothesis rule6 : Scottish -> WearKilt.

Lemma NoMember : False.
Tauto.
Save.

End club.

(**** Use of Intuition ****)
Lemma intu0:(((x:nat)(P x)) /\ B) ->
              (((y:nat)(P y)) /\ (P O)) \/ (B /\ (P O)).
Proof.
  Intuition.
Save.

Lemma intu1:((A:Prop)A\/~A)->(x,y:nat)(x=y\/~x=y).
Proof.
  Intuition.
Save.

