(* Test surgical use of beta-iota in the type of variables coming from
   pattern-matching for refine *)

Goal forall x : sigT (fun x => x = 1), True.
  intro x; refine match x with
                  | existT _ x' e' => _
                  end.
  lazymatch goal with
  | [ H : _ = _ |- _ ] => idtac
  end.
