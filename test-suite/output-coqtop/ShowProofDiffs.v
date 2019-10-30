(* coq-prog-args: ("-color" "on" "-diffs" "on") *)
Lemma x: forall(i : nat), exists(j k : nat), i = j /\ j = k /\ i = k.
Proof using.
  eexists.  Show Proof Diffs.
  eexists.  Show Proof Diffs.
  split.  Show Proof Diffs.
