(* The kernel may convert application arguments right to left,
   resulting in ill-typed terms, but should be robust to them. *)

Inductive Hide := hide : forall A, A -> Hide.

Lemma foo : (hide Type Type) = (hide (nat -> Type) (fun x : nat => Type)).
Proof.
  Fail reflexivity.
  match goal with |- ?l = _ => exact_no_check (eq_refl l) end.
  Fail Defined.
Abort.

Definition HideMore (_:Hide) := 0.

Definition foo : HideMore (hide Type Type) = HideMore (hide (nat -> Type) (fun x : nat => Type))
  := eq_refl.
