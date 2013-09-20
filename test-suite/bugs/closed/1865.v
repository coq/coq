(* Check that tactics (here dependent inversion) do not generate
   conversion problems T <= U with sup's of universes in U *)

(* Submitted by David Nowak *)

Inductive list (A:Set) : nat -> Set :=
| nil : list A O
| cons : forall n, A -> list A n -> list A (S n).

Definition f (n:nat) : Type :=
  match n with
  | O => bool
  | _ => unit
  end.

Goal forall A n, list A n -> f n.
intros A n.
dependent inversion n.
