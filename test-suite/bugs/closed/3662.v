Set Primitive Projections.
Set Implicit Arguments.
Set Nonrecursive Elimination Schemes.
Record prod A B := pair { fst : A ; snd : B }.
Definition f : Set -> Type := fun x => x.

Goal (fst (pair (fun x => x + 1) nat) 0) = 0.
compute.
Undo.
cbv.
Undo.
Opaque fst.
cbn.
Transparent fst.
cbn.
Undo.
simpl.
Undo.
Abort.

Goal f (fst (pair nat nat)) = nat.
compute.
  match goal with
    | [ |- fst ?x = nat ] => fail 1 "compute failed"
    | [ |- nat = nat ] => idtac
  end.
  reflexivity.
Defined.

Goal fst (pair nat nat) = nat.
  unfold fst. 
  match goal with
    | [ |- fst ?x = nat ] => fail 1 "compute failed"
    | [ |- nat = nat ] => idtac
  end.
  reflexivity.
Defined.

Lemma eta A B : forall x : prod A B, x = pair (fst x) (snd x). reflexivity. Qed.

Goal forall x : prod nat nat, fst x = 0.
  intros. unfold fst.
  Fail match goal with
    | [ |- fst ?x = 0 ] => idtac
  end.
Abort.

