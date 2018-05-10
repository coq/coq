(* Check that the subterms of the predicate of a match are taken into account *)

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
    | [ |- context G[@hd] ] => idtac
  end.
Abort.

(* This second example comes from CFGV where inspecting subterms of a
   match is expecting to inspect first the term to match (even though
   it would certainly be better to provide a "match x with _ end"
   construct for generically matching a "match") *)

Ltac find_head_of_head_match T :=
  match T with context [?E] => 
    match T with  
    | E => fail 1 
    | _ => constr:(E) 
    end 
  end.

Ltac mydestruct :=
  match goal with 
  | |- ?T1 = _ => let E := find_head_of_head_match T1 in destruct E
  end.

Goal forall x, match x with 0 => 0 | _ => 0 end = 0.
intros.
mydestruct.
Abort.
