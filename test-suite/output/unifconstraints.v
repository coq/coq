(* -*- coq-prog-args: ("-async-proofs" "no") -*- *)
(* Set Printing Existential Instances. *)
Unset Solve Unification Constraints.
Axiom veeryyyyyyyyyyyyloooooooooooooonggidentifier : nat.
Goal True /\ True /\ True \/
             veeryyyyyyyyyyyyloooooooooooooonggidentifier =
             veeryyyyyyyyyyyyloooooooooooooonggidentifier.
  refine (nat_rect _ _ _ _).
  Show.
Admitted.

Set Printing Existential Instances.
Goal forall n m : nat, True /\ True /\ True \/
                        veeryyyyyyyyyyyyloooooooooooooonggidentifier =
                        veeryyyyyyyyyyyyloooooooooooooonggidentifier.
  intros.
  refine (nat_rect _ _ _ _).
  Show.
  clear n. 
  Show.
  3:clear m.
  Show.
Admitted.
Unset Printing Existential Instances.

(* Check non regression of error message (the example can eventually
   improve though and succeed) *)

Fail Check fun (P : _ -> Type) (x:nat) (h:P x) => exist _ x (h : P x).

(* A test about universe level unification in congruence *)

Set Universe Polymorphism.
Section S.
Polymorphic Universes i j.
Goal Type@{i} -> (Type@{j} : Type@{i}).
Fail congruence.
Abort.
End S.
