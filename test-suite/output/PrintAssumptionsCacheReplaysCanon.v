(* Module aliases, functor applications, sealing and Include give objects
   whose canonical names differ under one user name. An entry is used only for
   the canonical name it was recorded under, so which objects are replayed
   here depends on that check, even though the output does not. *)

Set Debug "assumptions-cache".

Axiom ax : nat.

Module Type T.
  Parameter c : nat.
  Parameter d : nat.
End T.

Module M : T.
  Definition c := ax.
  Definition d := c.
End M.

Module MA := M.

Module F (X : T) : T.
  Definition c := X.c.
  Definition d := X.d + c.
End F.

Module P := F M.
Module Q := F MA.

Module G (X : T).
  Definition e := X.d.
  Module Inner := X.
  Definition f := Inner.c.
End G.

Module R := G M.
Module S := G MA.

Module Type U.
  Include T.
  Definition g := c + d.
End U.

Module V : U.
  Definition c := ax.
  Definition d := 0.
  Definition g := c + d.
End V.

Module W <: U := V.
Module Z := W.

Definition use := M.c + MA.c + P.c + Q.d + R.e + S.f + V.g + W.g + Z.g + R.f + S.e.
Print Assumptions use.
Print Assumptions MA.d.
Print Assumptions Q.d.
Print Assumptions S.f.
Print Assumptions Z.g.
Print Assumptions use.
Print All Dependencies use.

Module Inside.
  Print Assumptions use.
  Print Assumptions use.
End Inside.

Module Include1.
  Include P.
  Definition h := c + d.
  Print Assumptions h.
  Print Assumptions h.
End Include1.
Print Assumptions Include1.h.
Print Assumptions Include1.h.
Print Assumptions use Include1.h.
