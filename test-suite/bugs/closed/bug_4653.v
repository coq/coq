Definition T := Type.
Module Type S. Parameter foo : let A := T in True. End S.
Module M <: S. Lemma foo (A := T) : True. Proof I. End M.
