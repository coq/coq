(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
Require PolyList.

Parameter in_list : (list nat*nat)->nat->Prop.
Definition not_in_list : (list nat*nat)->nat->Prop
	:= [l,n]~(in_list l n).

(* Hints Unfold not_in_list. *)

Axiom lem1 : (l1,l2:(list nat*nat))(n:nat)
		(not_in_list (app l1 l2) n)->(not_in_list l1 n).

Axiom lem2 : (l1,l2:(list nat*nat))(n:nat)
		(not_in_list (app l1 l2) n)->(not_in_list l2 n).

Axiom lem3 : (l:(list nat*nat))(n,p,q:nat)
		(not_in_list (cons (p,q) l) n)->(not_in_list l n).

Axiom lem4 : (l1,l2:(list nat*nat))(n:nat)
	(not_in_list l1 n)->(not_in_list l2 n)->(not_in_list (app l1 l2) n).

Hints Resolve lem1 lem2 lem3 lem4: essai.

Goal (l:(list nat*nat))(n,p,q:nat)
		(not_in_list (cons (p,q) l) n)->(not_in_list l n).
Intros.
EAuto with essai.
Save.

(* Example from Nicolas Magaud on coq-club - Jul 2000 *)

Definition Nat: Set := nat.
Parameter S':Nat ->Nat.
Parameter plus':Nat -> Nat ->Nat.

Lemma simpl_plus_l_rr1:
  ((n0:Nat) ((m, p:Nat) (plus' n0 m)=(plus' n0 p) ->m=p) ->
   (m, p:Nat) (S' (plus' n0 m))=(S' (plus' n0 p)) ->m=p) ->
  (n:Nat) ((m, p:Nat) (plus' n m)=(plus' n p) ->m=p) ->
  (m, p:Nat) (S' (plus' n m))=(S' (plus' n p)) ->m=p.
Intros.
EAuto. (* does EApply H *) 
Qed.
