From Stdlib Require Import Ring.
Lemma Rlt_n_Sn : exists P:Prop, True -> P.
Proof.
eexists.
intro.
apply f_equal.
try ring_simplify.
Abort.
