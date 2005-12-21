Require Import List.

Check
  (fix F (A B : Set) (f : A -> B) (l : list A) {struct l} : 
   list B := match l with
             | nil => nil
             | a :: l => f a :: F _ _ f l
             end).

(* V8 printing of this term used to failed in V8.0 and V8.0pl1 (cf bug #860) *)
Check
  let fix f (m : nat) : nat :=
    match m with
    | O => 0
    | S m' => f m'
    end
  in f 0.

