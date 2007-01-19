(* Circular substitution check in subtyping verification *)
Module Type S. End S.
Module Type T. Declare Module M:S. End T.

Module N:S. End N.
Module NN <: T. Module M:=N. End NN.
Module P <: T with Module M:=NN := NN.
