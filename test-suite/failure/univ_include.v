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
Print Universes. (* constraint lost! *)

Module Mt.
  Definition t :=T.
End Mt.

Module P := G Mt.
Eval cbv delta [P.elt Mt.t] in P.elt.


