(* Catching PatternMatchingFailure was lost at some point *)
Goal nat -> True.
Fail intros [=].
