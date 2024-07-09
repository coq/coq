Set Universe Polymorphism.

Inductive Box@{s|u|} (A:Type@{s|u}) : Type@{s|u} :=
| box : A -> Box A.
Arguments box {_} _.

Definition apply aT rT (f : aT -> rT) u : rT :=
  match u with | box a => f a end.

(* In coq 8.19.0 *)
(* Incorrect elimination of "u" in the inductive type "Box": *)
(* the return type has sort "Type" while it should be at some variable quality. *)
(* Elimination of an inductive object of sort Type *)
(* is not allowed on a predicate in sort Type *)
(* because wrong arity. *)

(* In coq master eb4169c898e02f08b243b03b8d00c8cf7a353828 *)
(* Incorrect elimination of "u" in the inductive type "Box@{α71 | flabule.71}": *)
(* the return type has sort "Type@{α72 | flabule.69}" *)
(* while it should be in sort quality α71. *)
(* Elimination of a sort polymorphic inductive object instantiated to a variable sort quality *)
(* is only allowed on a predicate in the same sort quality. *)
