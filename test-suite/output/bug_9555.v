Module Type S. Axiom T : Type. Axiom a : T. End S.
Module Type F (X : S) := S.
Print Module Type F.
