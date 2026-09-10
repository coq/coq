(* An inline body must survive the transfer through a module alias.

   [F]'s parameter declares [Inline t], so applying it installs an inline body
   for that field. When the argument is an alias -- [B := A] -- the resolver of
   the application also records an equivalence pointing into [A], and the two
   hints land on the same key. [Mod_subst.subst_mp_delta] used to transfer an
   [InlineBody] as its alias alone; since [Deltamap.join] prefers the bindings
   of its first argument, that stripped hint then shadowed the body rather than
   merely failing to carry it.

   The visible symptom is that the objects attached to the field are no longer
   replayed onto the application: [R.u] loses the argument scope [A.u] has, so
   [1] is read in the ambient scope -- as [true] here -- instead of [nat_scope].
   Applying [F] to [A] directly is unaffected, and would mask the bug in this
   file by registering the scope under the shared canonical name. *)

Module Type T.
Parameter Inline t : Type.
Parameter u : t -> t.
End T.

Module A.
Definition t := nat.
Definition u (x : nat) := x.
End A.

Module B := A.
Module C := B.

Module F (X : T) := X.

Module R := F B.
Module S := F C.

Notation "1" := true.

Check R.u 1.
Check S.u 1.
