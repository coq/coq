(* The canonical name a delta-resolver assigns must itself be canonical.

   [Include Inner] gives [Outer.M] two pieces of information: the modpath
   equivalence [Outer.M ↦ Outer.Inner.M] and the kername equivalence
   [Outer.M.n ↦ M0.n]. The former is canonical as a modpath, but the fields of
   [Outer.Inner.M] are *not* canonical (they come from [Include M0]), so the
   kername equivalence is strictly finer and cannot be recovered from the
   modpath one.

   [Mod_subst.subst_mp_delta] used to resolve the modpath and then keep only
   the equivalences rooted at its canonical form, dropping the ones rooted at
   the path it started from. [Outer.E.n] then got the canonical name
   [Outer.Inner.M.n], which is itself an alias of [M0.n], while the resolver of
   the enclosing [Outer] said [M0.n] and the two disagreeing views made the
   last definition below fail with

     Ill-formed constant Outer.E.n: expected canonical name
     Outer.Inner.M.n but found M0.n *)

Module Type T. Parameter n : bool. End T.
Module M0. Definition n := true. End M0.
Module Id (X : T) := X.

Module Outer.
  Module Inner.
    Module M. Include M0. End M.
  End Inner.
  Include Inner.
  Module E. Include Id Outer.M. End E.
End Outer.

Definition check : Outer.E.n = M0.n := eq_refl.
