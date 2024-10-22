(* nondiscriminated uses head const, ignores patterns *)
Theorem bar: 1=1.  reflexivity.  Qed.
Theorem bar2: 2=2.  reflexivity.  Qed.

Create HintDb db. (* not discriminated *)
Hint Resolve bar : db.
Hint Resolve bar2 : db.

Set Typeclasses Debug Verbosity 2.

Goal 3=3.
(* no matching; both theorems are tried. *)
Fail progress debug auto with db nocore.
Fail typeclasses eauto with db nocore.
Abort.
