From PrintAssumptionsVOK Require file1.

Lemma main : False.
Proof. apply file1.aux. Qed.

Print Assumptions main. (* this fails *)
