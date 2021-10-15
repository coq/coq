Goal True.
  let term := constr:(Nat.add (Nat.mul 0 1) 2 = 2) in
  let term := lazymatch (eval pattern Nat.add, Nat.mul, S in term) with
              | ?term _ _ _ => term
              end in
  let term := lazymatch term with
              | fun (a : ?A) (b : ?B) (c : ?C) => ?term
                => constr:(fun (a : A) (b : B) (c : C) => term)
              end in
  idtac term; (* (fun (_ _ : nat -> nat -> nat) (n1 : nat -> nat) =>
 n1 (n1 0 (n1 0)) (n1 (n1 0)) = n1 (n1 0)) *)
    assert (H : { T : Type & T }) by abstract (eexists; exact term).
  (* Error: Illegal application (Non-functional construction):
The expression "n1" of type "nat -> nat"
cannot be applied to the terms
 "0" : "nat"
 "n1 0" : "nat" *)
  exact I.
Defined.
