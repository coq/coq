Require Import ssreflect.
Lemma toto (P Q:Prop) : P -> Q.
suff h : P.
Abort.
