Require Import ssreflect.

Inductive body :=
 mk_body : bool -> nat -> nat -> body.

Axiom big : (nat -> body) -> nat.

Axiom eq_big :
 forall P Q F G,
(forall x, P x = Q x :> bool) ->
 (forall x, (P x =true -> F x = G x : Type)) ->
  big (fun x => mk_body (P x) (F x) x) = big (fun toto => mk_body (Q toto) (F toto) toto).

Axiom leb : nat -> nat -> bool.

Axiom admit : False.

Lemma test :
  (big (fun x => mk_body (leb x 3) (S x + x) x))
 = 3.
Proof.

 under i : {1}eq_big.
  { by apply over. }
  { move=> Pi. by apply over. }
 rewrite /=.

 case: admit.
Qed.
