(* Support for complex constructions in recursive notations, especially "match". *)

Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x := let y := x in f y.
Notation "'dlet' x , y := v 'in' ( a , b , .. , c )"
  := (Let_In v (fun '(x, y) => pair .. (pair a b) .. c))
       (at level 0).
