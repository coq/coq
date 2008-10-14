Require Import Arith Omega.

Lemma test : forall p:nat, p<>0 -> p-1+1=p.
Proof.
 intros; omega.
Qed.

(** Test of new syntax for rewrite : ! ? and so on... *)

Lemma but : forall a b c, a<>0 -> b<>0 -> c<>0 ->
 (a-1+1)+(b-1+1)+(c-1+1)=a+b+c.
Proof.
intros.
rewrite test.
Undo.
rewrite test,test.
Undo.
rewrite 2 test. (* or rewrite 2test or rewrite 2!test *)
Undo.
rewrite 2!test,2?test.
Undo.
(*rewrite 4!test.  --> error *)
rewrite 3!test.
Undo.
rewrite <- 3?test.
Undo.
(*rewrite <-?test. --> loops*)
rewrite !test by auto.
reflexivity.
Qed.
