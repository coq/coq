Require Import List.
Open Scope list_scope.
Goal forall A (x x' : A) (xs xs' : list A) (H : x::xs = x'::xs'),
       let k :=
           (match H in (_ = y) return x = hd x y with
              | eq_refl => eq_refl
            end : x = x')
       in k = k.
  simpl.
  intros.
  match goal with
    | [ |- appcontext G[@hd] ] => idtac
  end.
