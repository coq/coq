Class Inhabited (A:Type) := {repr : A}.

(* Removing this instance gets rid of the bug *)
#[local] Instance Inhabited_option A : Inhabited (option A) := {repr := None}.

Lemma option_refl {A}: forall `{Inhabited A} (u : A), u = u.
Proof. reflexivity. Qed.

Succeed #[local] Hint Rewrite @option_refl : core.
Fail #[local] Hint Rewrite option_refl : core.
