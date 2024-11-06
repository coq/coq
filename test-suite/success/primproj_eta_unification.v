#[projections(primitive)] Record T := mkT {
  fst : nat ;
  snd : nat
}.

(* Eta-expansion in unification *)
Check eq_refl : mkT (fst ?[e]) (snd ?e) = mkT 1 2.

(* Eta-expansion in tactic-unification *)
Goal {e : T & mkT (fst e) (snd e) = mkT 1 2}.
Proof.
  econstructor.
  reflexivity.
Qed.
