(* Check the behaviour of Discriminate *)

(* Check that Discriminate tries Intro until *)

Lemma l1 : O=(S O)->False.   
Discriminate 1.
Qed.

Lemma l2 : (H:O=(S O))H==H.   
Discriminate H.
Qed.
