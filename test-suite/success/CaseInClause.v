(* in clause pattern *)
Require Vector.
Check (fun n (x: Vector.t True (S n)) =>
  match x in Vector.t _ (S m) return True with
    |Vector.cons _ h _ _ => h
  end).

(* Notation *)
Import Vector.VectorNotations.
Notation "A \dots n" := (Vector.t A n) (at level 200).
Check (fun m (x: Vector.t nat m) =>
  match x in _ \dots k return Vector.t nat (S k) with
    | Vector.nil _ => 0 :: []
    | Vector.cons _ h _ t => h :: h :: t
  end).

(* N should be a variable and not the inductiveRef *)
Require Import NArith.
Theorem foo : forall (n m : nat) (pf : n = m),
                match pf in _ = N with 
                  | eq_refl => unit
                end.
