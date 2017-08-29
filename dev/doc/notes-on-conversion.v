(**********************************************************************)
(* A few examples showing the current limits of the conversion algorithm *)
(**********************************************************************)

(*** We define (pseudo-)divergence from Ackermann function ***)

Definition ack (n : nat) :=
  (fix F (n0 : nat) : nat -> nat :=
     match n0 with
     | O => S
     | S n1 =>
         fun m : nat =>
         (fix F0 (n2 : nat) : nat :=
            match n2 with
            | O => F n1 1
            | S n3 => F n1 (F0 n3)
            end) m
     end) n.

Notation OMEGA := (ack 4 4).

Definition f (x:nat) := x.

(* Evaluation in tactics can somehow be controlled *)
Lemma l1 : OMEGA = OMEGA.
reflexivity.  (* succeed: identity *)
Qed.          (* succeed: identity *)

Lemma l2 : OMEGA = f OMEGA.
reflexivity.  (* fail: conversion wants to convert OMEGA with f OMEGA *)
Abort.        (* but it reduces the right side first! *)

Lemma l3 : f OMEGA = OMEGA.
reflexivity.  (* succeed: reduce left side first *)
Qed.          (* succeed: expected concl (the one with f) is on the left *)

Lemma l4 : OMEGA = OMEGA.
assert (f OMEGA = OMEGA) by reflexivity. (* succeed *)
unfold f in H.   (* succeed: no type-checking *)
exact H.         (* succeed: identity *)
Qed.             (* fail: "f" is on the left *)

(* This example would fail whatever the preferred side is *)
Lemma l5 : OMEGA = f OMEGA.
unfold f.
assert (f OMEGA = OMEGA) by reflexivity.
unfold f in H.
exact H.
Qed. (* needs to convert (f OMEGA = OMEGA) and (OMEGA = f OMEGA) *)

(**********************************************************************)
(* Analysis of the inefficiency in Nijmegen/LinAlg/LinAlg/subspace_dim.v *)
(* (proof of span_ind_uninject_prop *)

In the proof, a problem of the form   (Equal S t1 t2)
is "simpl"ified, then "red"uced to    (Equal S' t1 t1)
where the new t1's are surrounded by invisible coercions.
A reflexivity steps conclude the proof.

The trick is that Equal projects the equality in the setoid S, and
that (Equal S) itself reduces to some (fun x y => Equal S' (f x) (g y)).

At the Qed time, the problem to solve is (Equal S t1 t2) = (Equal S' t1 t1)
and the algorithm is to first compare S and S', and t1 and t2.
Unfortunately it does not work, and since t1 and t2 involve concrete
instances of algebraic structures, it takes a lot of time to realize that
it is not convertible.

The only hope to improve this problem is to observe that S' hides
(behind two indirections) a Setoid constructor. This could be the
argument to solve the problem.


