Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Universes.

Module Simple.

  (* in the real world foo@{i} might be [@paths@{i} nat] I guess *)
  Inductive foo : nat -> Type :=.

  (* on [refl (fun x => f x)] this computes to [refl f] *)
  Definition eta_out {A B} (f g : forall x : A, B x) (e : (fun x => f x) = (fun x => g x)) : f = g.
  Proof.
    change (f = g) in e. destruct e;reflexivity.
  Defined.

  Section univs.
    Universes i j.
    Constraint i < j. (* fail instead of forcing equality *)

    Definition one : (fun n => foo@{i} n) = fun n => foo@{j} n := eq_refl.

    Definition two : foo@{i} = foo@{j} := eta_out _ _ one.

    Definition two' : foo@{i} = foo@{j} := Eval compute in two.

    Definition three := @eq_refl (foo@{i} = foo@{j}) two.
    Definition four := Eval compute in three.

    Definition five : foo@{i} = foo@{j} := eq_refl.
  End univs.

  (* inference tries and succeeds with syntactic equality which doesn't eta expand *)
  Fail Definition infer@{i j k|i < k, j < k, k < eq.u0}
    : foo@{i} = foo@{j} :> (nat -> Type@{k})
    := eq_refl.

End Simple.

Module WithRed.
  (** this test needs to reduce the parameter's type to work *)


  Inductive foo@{i j} (b:bool) (x:if b return Type@{j} then Type@{i} else nat) : Type@{i} := .

  (* on [refl (fun x => f x)] this computes to [refl f] *)
  Definition eta_out {A B} (f g : forall x : A, B x) (e : (fun x => f x) = (fun x => g x)) : f = g.
  Proof.
    change (f = g) in e. destruct e;reflexivity.
  Defined.

  Section univs.
    Universes i j k.
    Constraint i < j. (* fail instead of forcing equality *)

    Definition one : (fun n => foo@{i k} false n) = fun n => foo@{j k} false n := eq_refl.

    Definition two : foo@{i k} false = foo@{j k} false := eta_out _ _ one.

    Definition two' : foo@{i k} false = foo@{j k} false := Eval compute in two.

    (* Failure of SR doesn't just mean that the type changes, sometimes
     we lose being well-typed entirely. *)
    Definition three := @eq_refl (foo@{i k} false = foo@{j k} false) two.
    Definition four := Eval compute in three.

    Definition five : foo@{i k} false = foo@{j k} false := eq_refl.
  End univs.

  (* inference tries and succeeds with syntactic equality which doesn't eta expand *)
  Fail Definition infer@{i j k|i < k, j < k, k < eq.u0}
    : foo@{i k} false = foo@{j k} false :> (nat -> Type@{k})
    := eq_refl.

End WithRed.
