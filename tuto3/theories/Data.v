Require Import ArithRing.

Class EvenNat the_even := {half : nat; half_prop : 2 * half = the_even}.

Instance EvenNat0 : EvenNat 0 := {half := 0; half_prop := eq_refl}.

Lemma even_rec n h : 2 * h = n -> 2 * S h = S (S n).
Proof. intros H; ring [H]. Qed.

Instance EvenNat_rec n (p : EvenNat n) : EvenNat (S (S n)) :=
 {half := S (@half _ p); half_prop := even_rec n (@half _ p) (@half_prop _ p)}.


Definition tuto_div2 n (p : EvenNat n) := @half _ p.

Record S_ev n := Build_S_ev {double_of : nat; s_h_prop : 2 * n = double_of}.

Canonical Structure can_ev0 : S_ev 0 :=
  Build_S_ev 0 0 (@eq_refl _ 0).

Lemma can_ev_rec n : forall (s : S_ev n), S_ev (S n).
Proof.
intros s; exists (S (S (double_of _ s))).
destruct s as [a P]. simpl. ring [P].
Defined.

Canonical Structure can_ev_rec.

Canonical Structure can_ev_default n d (Pd : 2 * n = d) : S_ev n :=
  Build_S_ev n d Pd.

