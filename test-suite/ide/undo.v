(* Here are a sequences of scripts to test interactively with undo and
   replay in coqide proof sessions *)

(* Undoing arbitrary commands, as first step *)

Theorem a : O=O.
Ltac f x := x.
assert True by trivial.
trivial.
Qed.

(* Undoing arbitrary commands, as non-first step *)

Theorem b : O=O.
assert True by trivial.
Ltac g x := x.
assert True by trivial.
trivial.
Qed.

(* Undoing declarations, as first step *)
(* was bugged in 8.1 *)

Theorem c : O=O.
Inductive T : Type := I.
trivial.
Qed.

(* Undoing declarations, as first step *)
(* new in 8.2 *)

Theorem d : O=O.
Definition e := O.
Definition f := O.
assert True by trivial.
trivial.
Qed.

(* Undoing declarations, as non-first step *)
(* new in 8.2 *)

Theorem h : O=O.
assert True by trivial.
Definition i := O.
Definition j := O.
assert True by trivial.
trivial.
Qed.

(* Undoing declarations, interleaved with proof steps *)
(* new in 8.2 *)

Theorem k : O=O.
assert True by trivial.
Definition l := O.
assert True by trivial.
Definition m := O.
assert True by trivial.
trivial.
Qed.

(* Undoing declarations, interleaved with proof steps and commands *)
(* new in 8.2 *)

Theorem n : O=O.
assert True by trivial.
Definition o := O.
Ltac h x := x.
assert True by trivial.
Focus.
Definition p := O.
assert True by trivial.
trivial.
Qed.

(* Undoing declarations, not in proof *)

Definition q := O.
Definition r := O.

(* Bug 2082 : Follow the numbers *)

Variable A : Prop.
Variable B : Prop.

Axiom OR : A \/ B.

Lemma MyLemma2 : True.
proof.
per cases of (A \/ B) by OR.
suppose A.
    then (1 = 1).
    then H1 : thesis. (* 4 *)
    thus thesis by H1. (* 2 *)
suppose B. (* 1 *) (* 3 *)
    then (1 = 1).
    then H2 : thesis.
    thus thesis by H2.
end cases.
end proof.
Qed. (* 5 if you made it here, there is no regression *)

