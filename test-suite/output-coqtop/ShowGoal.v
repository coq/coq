Lemma x: forall(i : nat), exists(j k : nat), i = j /\ j = k /\ i = k.
Proof using.
  intros i.
  eexists ?[j].
  eexists ?[k].
  split.
    trivial.
  split.
    trivial.
Show Goal 13 at 5.
Show Goal 13 at 7.
Show Goal 13 at 9.
