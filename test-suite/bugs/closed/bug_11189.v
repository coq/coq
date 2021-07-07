Structure trivial_cs := { key : Type }.

Canonical Structure base : trivial_cs := {|key := unit|}.
Canonical Structure step {A : Type} (t : trivial_cs) : trivial_cs := {| key := A -> key t |}.

Definition test := fun (t : trivial_cs) (k : key t) => tt.

Check test (_) (fun x : unit => tt).

Check (fun (x : key _) => x tt).
