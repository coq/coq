From Coq Require Import ssreflect ssrfun.

(* We should be able to use Some_inj as a view: *)
Lemma foo (x y : nat) : Some x = Some y -> x = y.
Proof. by move/Some_inj. Qed.
