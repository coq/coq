Theorem foo : Set.
pose (b := True).
Fail let a := b in refine (?[a] -> ?[a] = 1).
(* only [a]: exact nat. *)
(* only [b]: exact 3. *)
(* Qed. *)
(* Print foo. *)
(* (* foo = let b := True in nat -> 3 = 1 : Set *) *)
