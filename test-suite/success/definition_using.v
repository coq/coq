Require Import Program.
Axiom bogus : Type.

Section A.
Variable x : bogus.

#[using="All"]
Definition c1 : bool := true.

#[using="All"]
Fixpoint c2 n : bool :=
  match n with
  | O => true
  | S p => c3 p
  end
with c3 n : bool :=
  match n with
  | O => true
  | S p => c2 p
end.

#[using="All"]
Definition c4 : bool. Proof. exact true. Qed.

#[using="All"]
Fixpoint c5 (n : nat) {struct n} : bool. Proof. destruct n as [|p]. exact true. exact (c5 p). Qed.

#[using="All", program]
Definition c6 : bool. Proof. exact true. Qed.

#[using="All", program]
Fixpoint c7 (n : nat) {struct n} : bool :=
  match n with
  | O => true
  | S p => c7 p
  end.

Fail #[using="dummy", program]
Fixpoint c7' (n : nat) {struct n} : bool :=
  match n with
  | O => true
  | S p => c7' p
  end.

Fail #[using="c7'", program]
Fixpoint c7' (n : nat) {struct n} : bool :=
  match n with
  | O => true
  | S p => c7' p
  end.

End A.

Check c1 : bogus -> bool.
Check c2 : bogus -> nat -> bool.
Check c3 : bogus -> nat -> bool.
Check c4 : bogus -> bool.
Check c5 : bogus -> nat -> bool.
Check c6 : bogus -> bool.
Check c7 : bogus -> nat -> bool.

Section B.

Variable a : bogus.
Variable h : c1 a = true.

#[using="a*"]
Definition c8 : bogus := a.

Collection ccc := a h.

#[using="ccc"]
Definition c9 : bogus := a.

#[using="ccc - h"]
Definition c10 : bogus := a.

End B.

Check c8 : forall a, c1 a = true -> bogus.
Check c9 : forall a, c1 a = true -> bogus.
Check c10: bogus -> bogus.
