
(* we could use the inductive type nat defined in Peano.v
this is just to have a stand alone file *)

Symbol nat : Set.
Symbol O : nat.
Symbol S : nat->nat.

Symbol plus AC > S : nat->nat->nat.

Rules [x,y:nat] {
  (plus O x) => x;
  (plus (S x) y) => (S (plus x y))
}.

Lemma com: (x,y:nat)(plus x y)=(plus y x).
Reflexivity.
Qed.

Symbol mult AC > O plus : nat->nat->nat.

Rules [x,y,z:nat] {
  (mult O x) => O;
  (mult (S x) y) => (plus y (mult x y));
  (mult (plus x y) z) => (plus (mult x z) (mult y z))
}.

Symbol False : Prop.

Symbol absurd : False->(P:Prop)P.

Symbol neg Antimon(1) > False : Prop->Prop.

Rules [P:Prop] { (neg P) => P->False }.

Symbol list Mon(1): Set->nat->Set.
Symbol nil : (A:Set)(list A O).
Symbol cons : (A:Set)A->(n:nat)(list A n)->(list A (S n)).

Symbol app : (A:Set)(n:nat)(list A n)->(p:nat)(list A p)->(list A (plus n p)).

Rules [A:Set;p,q,r:nat;l:(list A p);l':(list A q);l'':(list A r)]
  let A' := A, n := O, n' := (S p), n'' := (plus p q) in
{
  (app A n (nil A') p l) => l;
  (app A n' (cons A' x p l) q l') => (cons A x (app A p l q l'));
  (app A n'' (app A' p l q l') r l'')
    => (app A p l (plus q r) (app A q l' r l''))
}.
