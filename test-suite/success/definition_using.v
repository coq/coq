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

#[using="All"]
Definition c6 : bool. Proof. exact true. Qed.

#[using="All"]
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

Module TypeBehavior.

Section S.
Variables a : nat.
#[using="Type", warning="-non-recursive"]
Program Fixpoint b1 (n:nat) : nat := (fun _ => 0) a.
Program Fixpoint b2 (n:nat) : (fun X _ => X) nat a := 0.
Program Fixpoint b3 (n:nat) : (fun X _ => X) nat a := (fun _ => 0) a.
Program Definition c1 : nat := (fun _ => 0) a.
Program Definition c2 : (fun X _ => X) nat a := 0.
Program Definition c3 : (fun X _ => X) nat a := (fun _ => 0) a.
Fixpoint d1 (n:nat) : nat := (fun _ => 0) a.
Fixpoint d2 (n:nat) : (fun X _ => X) nat a := 0.
Fixpoint d3 (n:nat) : (fun X _ => X) nat a := (fun _ => 0) a.
Definition e1 : nat := (fun _ => 0) a.
Definition e2 : (fun X _ => X) nat a := 0.
Definition e3 : (fun X _ => X) nat a := (fun _ => 0) a.
End S.
(* Not clear what is most expected below... *)

(* Dependency in a with Program Fixpoint: the body is not reduced. *)
(* As of now, we don't seem to have such a case. *)
(* No dependency in a with Program Fixpoint, because both body and type are beta-reduced *)
Check b1 0 : nat.
Check b2 0 : nat.
Check b3 0 : nat.
(* With Program Definition, type is beta-reduced but not the body *)
Check c1 0 : nat.
Check c2 : nat.
Check c3 0 : nat.
(* With Definition/Fixpoint, neither body nor type are beta-reduced *)
Check d1 0 0 : nat.
Check d2 0 0 : nat.
Check d3 0 0 : nat.
Check e1 0 : nat.
Check e2 0 : nat.
Check e3 0 : nat.

End TypeBehavior.
