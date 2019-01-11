(* to be used e.g. in : coqtop -I src -R theories Tuto3 < theories/test.v *)

Require Import Tuto3.Loader.

(* This should print Type. *)
Tuto3_1.

(* This should print a term that contains an existential variable. *)
(* And then print the same term, where the variable has been correctly
   instantiated. *)
Tuto3_2.

Lemma tutu x y (A : 0 < x) (B : 10 < y) : True.
Proof.
pack hypothesis A.
(* Hypothesis A should have disappeared and a "packed_hyps" hypothesis
  should have appeared, with unreadable content. *)
pack hypothesis B.
(* Hypothesis B should have disappeared *)
destruct packed_hyps as [unpacked_hyps].
(* Hypothesis unpacked_hyps should contain the previous contents of A and B. *)
exact I.
Qed.
