Set Universe Polymorphism.
Set Printing Universes.
Unset Universe Minimization ToSet.


Definition foo : Type := nat.
About foo.
(* foo@{Top.1} : Type@{Top.1}*)
(* Top.1 |=  *)

Definition bar : foo -> nat.
Admitted.
About bar.
(* bar@{Top.2} : foo@{Top.2} -> nat *)
(* Top.2 |=  *)

Lemma baz@{i} : foo@{i} -> nat.
Proof.
  exact bar.
Defined.

Definition bar'@{i} : foo@{i} -> nat.
  intros f. exact 0.
Admitted.
About bar'.
(* bar'@{i} : foo@{i} -> nat *)
(* i |=  *)

Axiom f@{i} : Type@{i}.
(*
*** [ f@{i} : Type@{i} ]
(* i |=  *)
*)
