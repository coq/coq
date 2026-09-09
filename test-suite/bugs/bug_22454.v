(* A resolver records two independent facts about a kername: the canonical name
   of the constant, and -- in a substitution -- the body an inlinable field is
   to be replaced with. They used to share the kmap slot, so recording the body
   dropped the name, leaving it to be recovered by the prefix rule alone. That
   rule answers a name of the *source* module, one alias hop short of canonical,
   and [Mod_subst.subst_mp_delta] cannot transfer it either, transferring only
   equivalences (see bugs/bug_22412_2.v).

   The resolver of [Outer.E] then disagreed with [Outer]'s on the canonical name
   of [Outer.E.n], and the definition below was rejected with "Ill-formed
   constant Outer.E.n: expected canonical name Outer.Inner.M.n but found
   M0.n". *)

Module Type T.
  Parameter Inline n : bool.
End T.

Module M0.
  Definition n := false.
End M0.

Module Id (X : T) := X.

Module Outer.
  Module Inner.
    Module M.
      Include M0.
    End M.
  End Inner.

  Include Inner.

  Module E.
    Include Id Outer.M.
  End E.
End Outer.

Definition check : Outer.E.n = M0.n := eq_refl.
