Lemma a : True.
Proof.
assert True as H.
  abstract (trivial) using exported_seff.
exact H.
Fail Qed exporting a_subproof.
Qed exporting exported_seff.
Check ( exported_seff : True ).

Lemma b : True.
Proof.
assert True as H.
  abstract (trivial) using exported_seff2.
exact H.
Qed.

Fail Check ( exported_seff2 : True ).

