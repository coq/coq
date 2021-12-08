
Definition bug := Eval vm_compute in eq_rect.
(* bug:
Error: Illegal application (Type Error):
The term "eq" of type "forall A : Type, A -> A -> Prop"
cannot be applied to the terms
 "x" : "A"
 "P" : "A -> Type"
 "x0" : "A"
The 1st term has type "A" which should be coercible to
"Type".
*)
