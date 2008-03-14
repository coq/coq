(*subtyping verification in presence of  pseudo-circularity at functor application *)
Module Type S. End S.
Module Type T. Declare Module M:S. End T.
Module N:S. End N.

Module F (X:S) (Y:T with Module M:=X). End F.

Module G := F N N.