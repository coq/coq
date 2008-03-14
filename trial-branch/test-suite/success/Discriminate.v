(* Check the behaviour of Discriminate *)

(* Check that Discriminate tries Intro until *)

Lemma l1 : 0 = 1 -> False.   
 discriminate 1.
Qed.

Lemma l2 : forall H : 0 = 1, H = H.   
 discriminate H.
Qed.
