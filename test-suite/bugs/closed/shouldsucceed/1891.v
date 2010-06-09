(* Check evar-evar unification *)
 Inductive T (A: Set): Set := mkT: unit -> T A.

  Definition f (A: Set) (l: T A): unit := tt.

  Implicit Arguments f [A].

  Lemma L (x: T unit): (unit -> T unit) -> unit.
  Proof.
    refine (match x return _ with mkT n => fun g => f (g _) end).
    trivial.
  Qed.

