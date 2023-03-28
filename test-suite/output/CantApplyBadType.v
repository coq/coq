Universes u0 u1.
Constraint u1 <= u0.
Axiom idu1 : Type@{u1} -> Type@{u1}.
Universe u.
Constraint u = u0.

(* pretyping error *)
Fail Check idu1 Type@{u}.
(* The command has indeed failed with message:
The term "Type" has type "Type@{u+1}" while it is expected to have type
"Type@{u1}" (universe inconsistency: Cannot enforce u < u1 because u1 <= u0 = u).
 *)

(* kernel error *)
Fail Type ltac:(refine (idu1 _); exact_no_check Type@{u}).
(* The command has indeed failed with message:
Illegal application:
The term "idu1" of type "Type -> Type"
cannot be applied to the term
 "Type" : "Type"
This term has type "Type@{u+1}" which should be coercible to
"Type@{u1}".
*)

(* typing.ml error *)
Goal True.
  Fail let c := constr:(ltac:(refine (idu1 _); exact_no_check Type@{u})) in
  let _ := type of c in
  idtac.
  (* same as kernel *)
Abort.
