Set Universe Polymorphism.

Inductive Box@{s|u|} (A:Type@{s|u}) := box (_:A).

Definition t1@{s|u|} (A:Type@{s|u}) (x y : A) := box _ x.
Definition t2@{s|u|} (A:Type@{s|u}) (x y : A) := box _ y.

Check fun A:SProp => eq_refl : t1 A = t2 A. (* What is in "test-suite/success/sort_polymorphism.v" *)
Check fun (A : SProp) => (fun (x : t1 A = t2 A) => x) eq_refl. (* Slight variation *)
