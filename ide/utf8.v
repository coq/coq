(* Logic *)
Notation "∀ x : t , P" := (x:t)P (at level 1, x,t,P at level 10).
Notation "∃ x : t , P" := (EXT x:t|P) (at level 1, x,t,P at level 10).
Notation "x ∨ y" := (x \/ y) (at level 1, y at level 10).
Notation "x ∧ y" := (x /\ y) (at level 1, y at level 10).
Notation "x → y" := (x -> y) (at level 1, y at level 10).
Notation "x ↔ y" := (x <-> y) (at level 1, y at level 10).
Notation "⌉ x" := (~x) (at level 1, x at level 10).

(* Abstraction *)
Notation  "'λ' x : T , y" := ([x:T] y) (at level 1, x,T,y at level 10).
Notation  "'λ' x := T , y" := ([x:=T] y) (at level 1, x,T,y at level 10).

(* Arithmetic *)
Notation "x ≤ y" := (le x y) (at level 3, y at level 10).
Notation "x ≥ y" := (ge x y) (at level 3, y at level 10).

(* Require ZArith.
   Notation "x ≤ y" := (Zle x y) (at level 1, y at level 10).*)
