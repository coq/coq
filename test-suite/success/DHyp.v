HintDestruct Hypothesis a (le O ?) 3 (Inversion H).

Goal ~(le O (S O)).
Intro H.
DHyp H.
Qed.

HintDestruct Conclusion a (le O ?) 3 Constructor.

Goal (le O O).
DConcl.
Qed.
