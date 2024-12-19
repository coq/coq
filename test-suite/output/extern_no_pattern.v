(* Hint Extern with no pattern always selected *)
Theorem bar: 3=3.  reflexivity.  Qed.

Create HintDb db discriminated.
Hint Extern 1 => idtac "1"; fail : db.
Hint Extern 1 => idtac "2"; fail : db.
Hint Extern 2 => apply bar : db.
Set Typeclasses Debug Verbosity 2.


Goal 3=3.
(* all 3 Hint Extern are tried *)
Succeed progress debug auto with db nocore.
Succeed typeclasses eauto with db nocore.
Abort.
