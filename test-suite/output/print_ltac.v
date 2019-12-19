(* Testing of various things about Print Ltac *)
(* https://github.com/coq/coq/issues/10971 *)
Ltac t1 := time "my tactic" idtac.
Print Ltac t1.
Ltac t2 := let x := string:("my tactic") in idtac x.
Print Ltac t2.
Tactic Notation "idtacstr" string(str) := idtac str.
Ltac t3 := idtacstr "my tactic".
Print Ltac t3.
(* https://github.com/coq/coq/issues/9716 *)
Ltac t4 x := match x with ?A => constr:((A, A)) end.
Print Ltac t4.
