(* File reduced by coq-bug-finder from original input, then from 538 lines to 31 lines *)
Open Scope type_scope.
Global Set Primitive Projections.
Set Implicit Arguments.
Record sig (A : Type) (P : A -> Type) := exist { proj1_sig : A ; proj2_sig : P proj1_sig }.
Notation sigT := sig (only parsing).
Notation "{ x : A  & P }" := (sigT (fun x:A => P)) : type_scope.
Notation projT1 := proj1_sig (only parsing).
Notation projT2 := proj2_sig (only parsing).
Variables X : Type.
Variable R : X -> X -> Type.
Lemma dependent_choice :
  (forall x:X, {y : _ & R x y}) ->
  forall x0, {f : nat -> X & (f O = x0) * (forall n, R (f n) (f (S n)))}.
Proof.
  intros H x0.
  set (f:=fix f n := match n with O => x0 | S n' => projT1 (H (f n')) end).
  exists f.
  split.
  reflexivity.
  induction n; simpl in *.
  clear.
  apply (proj2_sig (H x0)).
  Undo.
  apply @proj2_sig. 
  

(* Toplevel input, characters 21-31:
Error: Found no subterm matching "proj1_sig ?206" in the current *)
