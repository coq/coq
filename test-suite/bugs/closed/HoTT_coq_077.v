Set Implicit Arguments.

Require Import Logic.

Set Asymmetric Patterns.
Set Nonrecursive Elimination Schemes.
Set Primitive Projections.

Record prod (A B : Type) : Type :=
  pair { fst : A; snd : B }.

Print prod_rect.
(** prod_rect =
fun (A B : Type) (P : prod A B -> Type)
  (f : forall (fst : A) (snd : B), P {| fst := fst; snd := snd |})
  (p : prod A B) =>
match p as p0 return (P p0) with
| {| fst := x; snd := x0 |} => f x x0
end
     : forall (A B : Type) (P : prod A B -> Type),
       (forall (fst : A) (snd : B), P {| fst := fst; snd := snd |}) ->
       forall p : prod A B, P p

Arguments A, B are implicit
Argument scopes are [type_scope type_scope _ _ _]
 *)

(* What I really want: *)
Definition prod_rect' A B (P : prod A B -> Type) (u : forall (fst : A) (snd : B), P (pair fst snd))
           (p : prod A B) : P p
  := u (fst p) (snd p).

Notation typeof x := (ltac:(let T := type of x in exact T)) (only parsing).

(* Check for eta *)
Check eq_refl : typeof (@prod_rect) = typeof (@prod_rect').

(* Check for the recursion principle I want *)
Check eq_refl : @prod_rect = @prod_rect'.
