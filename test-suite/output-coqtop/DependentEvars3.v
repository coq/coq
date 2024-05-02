Set Printing Dependent Evars Line.
Lemma x : (exists(n : nat), n = 5 \/ True) /\ (exists(m : nat), m = 6 \/ True).
Proof using.
  split.
    eexists.
    right.
