V7only [
HintDestruct Hypothesis h1 (le ? O) 3 [Fun I -> Inversion I ].

Lemma lem1 : ~(le (S O) O).
Intro H.
DHyp H.
Qed.

HintDestruct Conclusion h2 (le O ?) 3 [Constructor].

Lemma lem2 : (le O O).
DConcl.
Qed.
].
