Lemma test (X : nat -> Prop) (H : forall n, X n) (H' : forall n, X n -> X (S n)) : True.
Proof.
  specialize (H 5) as J%H'.
  Check (J : X 6).
  Fail Check H.
  Undo.
  specialize (H 5) as ?%H'.
  Check (H0 : X 6).
  Fail Check H.
Abort.

Lemma test2 (b : bool) (f : bool -> nat) : True.
Proof.
  specialize b as [|n]%f.
  Fail Check b.
  2:Check (n : nat).
Abort.

Lemma test3 (b : bool) (f : bool -> nat) : True.
Proof.
  specialize (f b) as f'.
  Check (f : bool -> nat).
  Undo.
  specialize (f b) as ?f.
  Check (f : bool -> nat).
  Check (f0 : nat).
  Undo.
  specialize (f b) as f.
  Check (f : nat).
Abort.
