(* show alternating separators in typeclass debug output; see discussion in PR #868 *)

Parameter foo : Prop.
Axiom H : foo -> foo.
Hint Resolve H : foo.
Goal foo.
Typeclasses eauto := debug.
Fail typeclasses eauto 5 with foo.
