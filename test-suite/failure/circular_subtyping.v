(* subtyping verification in presence of  pseudo-circularity*)
Module Type S. End S.
Module Type T. Declare Module M:S. End T.
Module N:S. End N.
Module NN <: T. Module M:=N. End NN.

Fail Module P <: T with Module M:=NN := NN.

Module F (X:S) (Y:T with Module M:=X). End F.
Fail Module G := F N N.
