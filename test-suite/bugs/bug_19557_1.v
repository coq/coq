Require Import ListDef Morphisms Setoid.

Global Generalizable All Variables.

Class Equiv A := equiv: relation A.

Section ops.
  Context (M : Type -> Type).

  Class MonadReturn := ret: forall {A}, A -> M A.

End ops.

Arguments ret {M MonadReturn A} _.


Class Monad (M : Type -> Type) `{forall A, Equiv A -> Equiv (M A)}
  `{MonadReturn M} : Prop :=
  {
    mon_ret_proper `{Equiv A} :: Proper (equiv ==> equiv) (@ret _ _ A)
  }.


Section S.
  Context `{Equivalence A eqA}.

  Inductive PermutationA : list A -> list A -> Prop := .

  Global Instance: Equivalence PermutationA.
  Admitted.

  Global Instance PermutationA_cons :
    Proper (eqA ==> PermutationA ==> PermutationA) (@cons A).
  Admitted.

  Lemma foo a l x (IHl : PermutationA (x::l) (l ++ (x :: nil))) : PermutationA (x::a::l) (a::l++(x :: nil)).
  Proof.
    rewrite <-IHl.
  Abort.
End S.
