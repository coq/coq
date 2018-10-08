Notation "P |-- Q" := (@eq nat P Q) (at level 80, Q at level 41, no associativity) .
Notation "x &&& y" := (plus x y) (at level 40, left associativity, y at next level) .
Notation "'Ex' x , P " := (plus x P) (at level 65, x at level 99, P at level 80).

(* Succeed *)
Check _ |-- _ &&& _ -> _.
Check _ |-- _ &&& (Ex _, _ ) -> _.
Check _ |-- (_ &&& Ex _, _ ) -> _.

(* Why does this fail? *)
Fail Check _ |-- _ &&& Ex _, _  -> _.
(* The command has indeed failed with message:
=> Error: The term "Ex ?17, ?18" has type "nat"
which should be Set, Prop or Type. *)

(* Just in case something is strange with -> *)
Notation "P ----> Q" := (P -> Q) (right associativity, at level 99, Q at next level).

(* Succeed *)
Check _ |-- _ &&& _ ----> _.
Check _ |-- _ &&& (Ex _, _ )  ----> _.
Check _ |-- (_ &&& Ex _, _ )  ----> _.

(* Why does this fail? *)
Fail Check _ |-- _ &&& Ex _, _  ----> _.
(* The command has indeed failed with message:
=> Error: The term "Ex ?31, ?32" has type "nat"
which should be Set, Prop or Type.*)
