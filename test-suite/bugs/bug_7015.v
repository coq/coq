Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Universes.

(* Contrarily to the original report, now the Simple test succeeds as i is seen
  as irrelevant even for a partial application. The second example still
  has a failing case because one needs to eta-expand it before i is considered
  irrelevant.  *)

Module Simple.

  (* in the real world foo@{i} might be [@paths@{i} nat] I guess *)
  Inductive foo@{i} : nat -> Type@{i} :=.

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

  (* inference tries and succeeds with syntactic equality but doesn't need eta expansion here *)
  Definition infer@{i j k|i < k, j < k, k < eq.u0}
    : foo@{i} = foo@{j} :> (nat -> Type@{k})
    := eq_refl.

End Simple.

Module WithRed.
  (** this test needs to reduce the parameter's type to work *)


  Inductive foo@{i} (b:bool) (x:if b return Type@{i+1} then Type@{i} else nat) : Type@{i} := .

  (* on [refl (fun x => f x)] this computes to [refl f] *)
  Definition eta_out {A B} (f g : forall x : A, B x) (e : (fun x => f x) = (fun x => g x)) : f = g.
  Proof.
    change (f = g) in e. destruct e;reflexivity.
  Defined.

  Section univs.
    Universes i j k.
    Constraint i < j. (* fail instead of forcing equality *)

    Definition one : (fun n => foo@{i} false n) = fun n => foo@{j} false n := eq_refl.

    Definition two : foo@{i} false = foo@{j} false := eta_out _ _ one.

    Definition two' : foo@{i} false = foo@{j} false := Eval compute in two.

    (* Failure of SR doesn't just mean that the type changes, sometimes
     we lose being well-typed entirely. *)
    Definition three := @eq_refl (foo@{i} false = foo@{j} false) two.
    Definition four := Eval compute in three.

    Definition five : foo@{i} false = foo@{j} false := eq_refl.
  End univs.

  (* inference tries and succeeds with syntactic equality which doesn't eta expand *)
  Fail Definition infer@{i j +|i < eq.u0, j < eq.u0}
    : foo@{i} false = foo@{j} false :> (nat -> Type@{max(i,j)})
    := eq_refl.

  (* inference backtracks on syntactic equality *)
  Definition infer@{i j|i < eq.u0, j < eq.u0}
    : foo@{i} false = foo@{j} false :> (nat -> Type@{max(i,j)})
    := eq_refl.

End WithRed.
