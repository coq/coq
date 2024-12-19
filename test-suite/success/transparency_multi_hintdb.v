(* constant transparent in one hintdb but not the other *)

Definition one := 1.
Theorem thm : one = 1. reflexivity. Qed.
Create HintDb db1 discriminated.
Hint Opaque one : db1.
Hint Resolve thm | 1 : db1.
Create HintDb db2 discriminated.

Goal 1 = 1.
Fail typeclasses eauto with db1 db2 nocore.
Succeed eauto with db1 db2 nocore.  (* bug! *)
Succeed auto with db1 db2 nocore.   (* bug! *)

Hint Resolve thm | 2 : db2.
Succeed typeclasses eauto with db1 db2 nocore.
Abort.
