
Set Printing Projections.
Set Primitive Projections.

Class HostFunction := host_func : Type.

Section store.
  Context `{HostFunction}.
  Record store := { store_funcs : host_func }.
End store.

Check (fun (S:@store nat) => S.(store_funcs)).

Module LocalDefUnfolding.

Unset Printing Projections.
Record U A (B:=A) C := {c:B*A*C;a:=(A,B,C,c);b:a=a}.
Print a.
Print b.

End LocalDefUnfolding.

Module Discharge.

Section A.
Record foo A := { bar : A}.
End A.
Definition bar' := bar.
Lemma f A x : bar' A x = bar A x.
unfold bar'.
Show. (* second should be the primitive construct *)
reflexivity.
Qed.

End Discharge.
