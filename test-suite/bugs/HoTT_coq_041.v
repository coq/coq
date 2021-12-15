Set Printing All.
Definition foo (s d : Prop)
 : ((s : Set) -> (d : Set)) = ((s : Prop) -> (d : Prop))
 := eq_refl. (* succeeds *)
Definition bar (s d : Prop)
 : ((fun x : Set => x) s -> (fun x : Set => x) d) = ((fun x : Prop => x) s -> (fun x : Prop => x) d)
 := eq_refl. (* Toplevel input, characters 131-138:
Error:
In environment
s : Prop
d : Prop
The term
 "@eq_refl Set (forall _ : (fun x : Set => x) s, (fun x : Set => x) d)"
has type "@eq Set (forall _ : s, d) (forall _ : s, d)"
while it is expected to have type
 "@eq Set (forall _ : s, d) (forall _ : s, d)"
(cannot unify "forall _ : (fun x : Set => x) s, (fun x : Set => x) d" and
"forall _ : (fun x : Prop => x) s, (fun x : Prop => x) d"). *)
