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




