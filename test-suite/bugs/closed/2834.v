(* Testing typing of subst *)

Lemma eqType2Set (a b : Set) (H : @eq Type a b) : @eq Set a b.
Fail subst.
