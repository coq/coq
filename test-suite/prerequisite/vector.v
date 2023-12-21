Module Vector.
Inductive t (A : Type) : nat -> Type :=
  | nil : t A 0
  | cons : A -> forall n : nat, t A n -> t A (S n).
Fixpoint map {A B} (f : A -> B) {n} (v : t A n) : t B n :=
  match v in (Vector.t _ n0) return (Vector.t B n0) with
  | nil _ => nil B
  | cons _ a n0 v' => cons B (f a) n0 (map f v')
  end.
Definition caseS {A} (P : forall {n}, t A (S n) -> Type)
    (H : forall h {n} t, @P n (cons _ h _ t)) {n} (v: t A (S n)) : P v :=
  match v with
  | cons _ h _ t => H h t
  | _ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
  end.
Definition tl {A} := @caseS _ (fun n v => t A n) (fun h n t => t).
End Vector.
