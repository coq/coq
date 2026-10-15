Axiom T : Type.

Declare Scope T_scope.
Bind Scope T_scope with T.
Delimit Scope T_scope with T.

Axiom g : T -> T -> Prop.

Set Warnings "+inconsistent-scopes".

(* x in empty stack or T_scope *)
Fail Abbreviation H F x := (g (F x) x%T).

(* x in T_scope or _T_scope + T_scope (questionable failure) *)
Fail Abbreviation H F x := (g (F x) x%_T)%T.

(* used to fail with x in T_scope or T_scope + T_scope, ie below text *)
Abbreviation H F x := (g (F x) x%T)%T.

(* Warning: Argument x was previously inferred to be in scope T_scope but is *)
(* here used in scope stack [T_scope, T_scope]. Scope T_scope will be used at *)
(* parsing time unless you override it by annotating the argument with an *)
(* explicit scope of choice. [inconsistent-scopes,syntax] *)
