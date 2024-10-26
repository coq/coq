(* Opacity per name *)
Fixpoint #[sealed] f n := match n with 0 => 0 | S n => g n end
with #[transparent] g n := match n with 0 => 0 | S n => f n end.

Fail Check eq_refl : f 0 = 0.
Check eq_refl : g 0 = 0.

(* Opacity globally *)
#[sealed]
Fixpoint f' n := match n with 0 => 0 | S n => g' n end
with g' n := match n with 0 => 0 | S n => f' n end.

Fail Check eq_refl : f' 0 = 0.
Fail Check eq_refl : g' 0 = 0.

(* Don't mix the global and local attribute *)
Fail #[sealed]
Fixpoint #[sealed] f' n := match n with 0 => 0 | S n => g' n end
with g' n := match n with 0 => 0 | S n => f' n end.

(* Other tests *)

#[sealed] Definition c := 0.

Fail Check eq_refl : c = 0.

#[transparent] Theorem u : nat. exact 0. Qed. (* ok *)
#[sealed] Definition v : nat. exact 0. Defined. (* ok *)

Check eq_refl : u = 0.
Fail Check eq_refl : v = 0.

#[sealed] Theorem w : nat. exact 0. Defined.
#[transparent] Definition x : nat. exact 0. Qed.

Fail Check eq_refl : w = 0.
Check eq_refl : x = 0.
