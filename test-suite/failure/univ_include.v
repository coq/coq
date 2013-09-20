Definition T := Type.
Definition U := Type.

Module Type MT.
  Parameter t : T.
End MT.

Module Type MU.
  Parameter t : U.
End MU.

Module F (E : MT).
  Definition elt :T := E.t.
End F.

Module G (E : MU).
  Include F E.
Print Universes. (* U <= T *)
End G.
Print Universes. (* Check if constraint is lost *)

Module Mt.
  Definition t := T.
End Mt.

Fail Module P := G Mt. (* should yield Universe inconsistency *)
(* ... otherwise the following command will show that T has type T! *)
(* Eval cbv delta [P.elt Mt.t] in P.elt. *)


