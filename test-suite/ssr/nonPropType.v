Require Import ssreflect.

(** Test the nonPropType interface and its application to prevent unwanted
    instantiations in views. **)

Lemma raw_flip {T} (x y : T) : x = y -> y = x. Proof. by []. Qed.
Lemma flip {T : nonPropType} (x y : T) : x = y -> y = x. Proof. by []. Qed.

Lemma testSet : true = false -> True.
Proof.
Fail move/raw_flip.
have flip_true := @flip _ true.
(* flip_true : forall y : notProp bool, x = y -> y = x *)
simpl in flip_true.
(* flip_true : forall y : bool, x = y -> y = x *)
by move/flip.
Qed.

Lemma override (t1 t2 : True) : t1 = t2 -> True.
Proof.
Fail move/flip.
by move/(@flip (notProp True)).
Qed.
