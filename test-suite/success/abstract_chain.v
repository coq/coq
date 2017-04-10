Lemma foo1 : nat -> True.
Proof.
intros _.
assert (H : True -> True).
{ abstract (exact (fun x => x)) using bar. }
assert (H' : True).
{ abstract (exact (bar I)) using qux. }
exact H'.
Qed.

Lemma foo2 : True.
Proof.
assert (H : True -> True).
{ abstract (exact (fun x => x)) using bar. }
assert (H' : True).
{ abstract (exact (bar I)) using qux. }
assert (H'' : True).
{ abstract (exact (bar qux)) using quz. }
exact H''.
Qed.

Set Universe Polymorphism.

Lemma foo3 : nat -> True.
Proof.
intros _.
assert (H : True -> True).
{ abstract (exact (fun x => x)) using bar. }
assert (H' : True).
{ abstract (exact (bar I)) using qux. }
exact H'.
Qed.

Lemma foo4 : True.
Proof.
assert (H : True -> True).
{ abstract (exact (fun x => x)) using bar. }
assert (H' : True).
{ abstract (exact (bar I)) using qux. }
assert (H'' : True).
{ abstract (exact (bar qux)) using quz. }
exact H''.
Qed.
