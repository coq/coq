

Inductive pack (A: Type) : Type :=
  packer : A -> pack A.

Arguments packer {A}.

Definition uncover (A : Type) (packed : pack A) : A :=
  match packed with packer v => v end.

Notation "!!!" := (pack _) (at level 0, only printing).

(* The following data is used as material for automatic proofs
  based on type classes. *)

Class EvenNat the_even := {half : nat; half_prop : 2 * half = the_even}.

#[export] Instance EvenNat0 : EvenNat 0 := {half := 0; half_prop := eq_refl}.
Register EvenNat as Tuto3.EvenNat.

Lemma even_rec n h : 2 * h = n -> 2 * S h = S (S n).
Proof.
  intros [].
  simpl. rewrite <-plus_n_O, <-plus_n_Sm.
  reflexivity.
Qed.

#[export] Instance EvenNat_rec n (p : EvenNat n) : EvenNat (S (S n)) :=
 {half := S (@half _ p); half_prop := even_rec n (@half _ p) (@half_prop _ p)}.

Definition tuto_div2 n (p : EvenNat n) := @half _ p.
Register tuto_div2 as Tuto3.tuto_div2.

(* to be used in the following examples
Compute (@half 8 _).

Check (@half_prop 8 _).

Check (@half_prop 7 _).

and in command Tuto3_3 8. *)

(* The following data is used as material for automatic proofs
  based on canonical structures. *)

Record S_ev n := Build_S_ev {double_of : nat; _ : 2 * n = double_of}.
Register S_ev as Tuto3.S_ev.

Definition s_half_proof n (r : S_ev n) : 2 * n = double_of n r :=
  match r with Build_S_ev _ _ h => h end.
Register s_half_proof as Tuto3.s_half_proof.

Canonical Structure can_ev_default n d (Pd : 2 * n = d) : S_ev n :=
  Build_S_ev n d Pd.

Canonical Structure can_ev0 : S_ev 0 :=
  Build_S_ev 0 0 (@eq_refl _ 0).

Lemma can_ev_rec n : forall (s : S_ev n), S_ev (S n).
Proof.
intros s; exists (S (S (double_of _ s))).
destruct s as [a P].
exact (even_rec _ _ P).
Defined.

Canonical Structure can_ev_rec.

Record cmp (n : nat) (k : nat) :=
  C {h : S_ev k; _ : double_of k h = n}.
Register C as Tuto3.C.

(* To be used in, e.g.,

Check (C _ _ _ eq_refl : cmp 6 _).

Check (C _ _ _ eq_refl : cmp 7 _).

*)
