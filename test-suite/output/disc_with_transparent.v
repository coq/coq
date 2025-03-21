(* discriminated database with transparent items in hints *)
From Corelib Require Import Nat.
Theorem bar: 1+1+1=3.  reflexivity.  Qed.
Theorem bar2: 3+1+1=5.  reflexivity.  Qed.

Definition one := 1.
Definition two := 2.
Definition one_plus_one_plus_one := 1+1+1.

Create HintDb db discriminated.
Hint Resolve bar | 2 : db.
Hint Resolve bar2 | 1 : db.
Hint Opaque Nat.add : db.
Set Typeclasses Debug Verbosity 2.

Goal two+1+1=5.
(* matches bar2, which fails in the tactic*)
Fail progress debug auto with db nocore.
Fail typeclasses eauto with db nocore.
Abort.

Goal 1+1+1=one.
(* matches bar, which fails in the tactic *)
Fail progress debug auto with db nocore.
Fail typeclasses eauto with db nocore.
Abort.

Goal two+1+1=one.
(* matches both bar and bar2, which both fail in the tactic *)
Fail progress debug auto with db nocore.
Fail typeclasses eauto with db nocore.
Abort.

Goal 1+1+1=1+1+1.
(* no match, fails *)
Fail progress debug auto with db nocore.
Fail typeclasses eauto with db nocore.
Abort.

Goal 1+1+1=one_plus_one_plus_one.
(* matches bar, succeeds because tactic uses conversion *)
Succeed progress debug auto with db nocore.

Succeed exact bar.
Succeed simple apply bar.
Fail autoapply bar with db.  (* a bug or poor documentation? *)

Set Typeclasses Debug Verbosity 2.
(* fails because tc eauto uses autoapply, copying that Nat.add is opaque *)
Fail typeclasses eauto with db nocore.
Abort.
