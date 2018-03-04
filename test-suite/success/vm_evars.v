Fixpoint iter {A} (n : nat) (f : A -> A) (x : A) :=
match n with
| 0 => x
| S n => iter n f (f x)
end.

Goal nat -> True.
Proof.
intros n.
evar (f : nat -> nat).
cut (iter 10 f 0 = 0).
vm_compute.
intros; constructor.
instantiate (f := (fun x => x)).
reflexivity.
Qed.

Goal exists x, x = 5 + 5.
Proof.
  eexists.
  vm_compute.
  reflexivity.
Qed.
