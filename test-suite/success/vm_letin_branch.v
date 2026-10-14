(* The VM and native readbacks of a match on a constructor with let-ins
   interleaved with its real arguments must map the branch's variables to
   the right binders. *)

Inductive A : Type := MkA (T := nat) (n : nat) (m := 0).

Inductive B : Type :=
  MkB (a := 0) (x : nat) (b := true) (y : bool) (c := 2) (z : nat) (d := 3).

Definition fA (p : A) := match p with MkA n => n end.
Definition fB (p : B) := match p with MkB x y z => (x, y, z) end.

Ltac check t :=
  let l := eval lazy in t in
  let v := eval vm_compute in t in
  let n := eval native_compute in t in
  constr_eq v l; constr_eq n l.

Goal True.
Proof.
  check (fun p => fA p).
  check (fun p => fB p).
  exact I.
Qed.

(* The readback used to be ill-typed, rejected at Qed. *)
Lemma lA : forall p, fA p = fA p.
Proof. intro p. vm_compute. exact eq_refl. Qed.

Lemma lB : forall p, fB p = fB p.
Proof. intro p. vm_compute. exact eq_refl. Qed.

Lemma lA' : forall p, fA p = fA p.
Proof. intro p. native_compute. exact eq_refl. Qed.

Lemma lB' : forall p, fB p = fB p.
Proof. intro p. native_compute. exact eq_refl. Qed.
