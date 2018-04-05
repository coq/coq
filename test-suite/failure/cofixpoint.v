(* A bug in the guard checking of nested cofixpoints. *)
(* Posted by Maxime Dénès on coqdev (Apr 9, 2014).    *)

Set Primitive Projections.
CoInductive CoFalse := { coFalse : False }.

CoInductive CoTrue := { coTrue : True }.

Fail CoFixpoint loop : CoFalse :=
  (cofix f := loop with g := loop for f).

Fail CoFixpoint loop : CoFalse :=
  (cofix f := I with g := loop for g).

Fail CoFixpoint loop : CoFalse :=
  (cofix f := loop with g := I for f).
