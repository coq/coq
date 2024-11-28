Section S.
  Hypothesis HypFalse : False.
  Lemma false_in_section : False.
  Proof using.
    abstract (apply HypFalse).
  (* in bad versions, both Qed and Fail Qed succeed
     (ie Qed fails when wrapped in Fail) *)
  Qed.
