(* Hint Extern uses syntactic unification *)
Definition one := 1.
Theorem bar: 1=one.  reflexivity.  Qed.

Create HintDb db discriminated.
Hint Extern 1 (1=one) => apply bar : db.

Set Typeclasses Debug Verbosity 2.

Goal one=1.
(* fail as expected; "one" is not expanded *)
Fail progress debug auto with db nocore.
Fail typeclasses eauto with db nocore.
Abort.
