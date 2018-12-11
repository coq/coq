Require Import ssreflect.

Axiom oops : 3=4.

Ltac ssrdone33 := exact: oops.

Lemma false : 5 = 6.
Proof.
congr (S (S _)).
Fail done.
move => /33/.
Qed.

Lemma false2 : 3 = 4 /\ 2 + 3 = 5.
Proof.
split => /33/=.
lazymatch goal with
| |- 2 + 3 = 5 => fail
| |- 5 = 5 => done
end.
Qed.

Ltac ssrsimpl7 := idtac.

Lemma test2 : 1+1 = 2.
Proof.
move=> /7=.
match goal with |- 1+1=2 => idtac end.
move=> /=.
match goal with |- 2=2 => reflexivity end.
Qed.

Lemma test3 : 1+1 = 2 /\ 3=4.
Proof.
split=> /33/7=.
match goal with |- 1+1=2 => idtac end.
move=> /=.
match goal with |- 2=2 => reflexivity end.
Qed.

Lemma test4 : 1+2 = 4 /\ 4=4.
Proof.
split=> //7=.
match goal with |- 1+2=4 => idtac end.
move=> /33/.
Qed.

Lemma test5 : 1=1 /\ 2=2.
Proof.
move=> /0/.
split=> /0/.
Qed.

Lemma test6 : True.
Proof. move => //. Qed.

Lemma test7 : 1 + 1 = 2.
Proof.
rewrite /7=.
reflexivity.
Qed.
