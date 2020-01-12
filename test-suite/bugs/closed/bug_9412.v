Module A.
Context (H : forall {n:nat}, n=n -> True).
Check H (n := 1).
Check H eq_refl.
Context (L := fun {x:nat} (H:x=x) => H).
About L.
Check L (x := 1).
Check L eq_refl.
End A.

Section S.
Context (H : forall {n:nat}, n=n -> True).
Check H (n := 1).
Check H eq_refl.
Context (L := fun {x:nat} (H:x=x) => H).
Check L (x := 1).
Check L eq_refl.
End S.
