Set Primitive Projections.
Set Implicit Arguments.
Set Universe Polymorphism.

Record category := { ob : Type }.

Goal forall C, ob C -> ob C.
intros C X.

let y := (eval compute in (ob C)) in constr_eq y (ob C). (* success *)
let y := (eval compute in (@ob C)) in constr_eq y (ob C). (* success *)
(* should be [Fail let y := (eval compute in (@ob C)) in constr_eq y (@ob C).] (really [let y := (eval compute in (@ob C)) in constr_eq y (@ob C)] should succeed, but so long as the [Fail] succeeds, this bug is open), but "not equal" escapes [Fail]. *)
try (let y := (eval compute in (@ob C)) in constr_eq y (@ob C); fail 1). (* failure *)
try (constr_eq (@ob C) (ob C); fail 1). (* failure *)
let y := constr:(@ob C) in
match y with
  | ?f C => idtac
end. (* success *)
try (let y := constr:(@ob C) in
match eval compute in y with
  | ?f C => idtac
end; fail 1). (* failure: no matching clauses for match *)
