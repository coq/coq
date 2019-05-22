Require Import ssreflect ssrfun ssrbool.

(** Test the various idioms that control rewriting in boolean predicate. **)

Definition simpl_P := [pred a | ~~ a].
Definition nosimpl_P : pred bool := [pred a | ~~ a].
Definition coll_P : collective_pred bool := [pred a | ~~ a].
Definition appl_P : applicative_pred bool := [pred a | ~~ a].
Definition can_appl_P : pred bool := [pred a | ~~ a].
Canonical register_can_appl_P := ApplicativePred can_appl_P.
Ltac see_neg := (let x := fresh "x" in set x := {-}(~~ _); clear x).

Lemma test_pred_rewrite (f := false) : True.
Proof.
have _: f \in simpl_P by rewrite inE; see_neg.
have _ a: simpl_P (a && f) by simpl; see_neg; rewrite andbF.
have _ a: simpl_P (a && f) by rewrite inE; see_neg; rewrite andbF.
have _: f \in nosimpl_P by rewrite inE; see_neg.
have _: nosimpl_P f. simpl. Fail see_neg. Fail rewrite inE. done.
have _: f \in coll_P. Fail rewrite inE. by rewrite in_collective; see_neg.
have _: f \in appl_P.
  rewrite inE. Fail see_neg. Fail rewrite inE. simpl. Fail see_neg.
  Fail rewrite app_predE. done.
have _: f \in can_appl_P.
  rewrite inE. Fail see_neg. Fail rewrite inE. simpl. Fail see_neg.
  by rewrite app_predE in_simpl; see_neg.
done.
Qed.
