(* Guards against over-fixing the [subst_mp_delta] bug.

   The fix transfers the equivalences [resolve] records under [mp'] over to
   [mkey], but only the [Equiv] ones.  Transferring the [Inline] ones as well,
   which is what the obvious keep-everything-under-[mp'] version does,
   breaks this program. *)

Module Type T. Parameter Inline n : bool. End T.
Module M. Definition n := false. End M.
Module F (X : T).
  Definition n := X.n.
  Module Alias := X.
End F.
Module R1 := F M.
Module R2 := F R1.Alias.
Module R3 := F R2.
Module Type S. Module B := R3.Alias. End S.
Module G (X : S). End G.
Module A : S. Module B := R3.Alias. End A.
Module R4 := G A.
