Section Lists.
  Context [A : Type].

  Fixpoint In (a : A) (l : list A) : Prop :=
    match l with
    | nil => False
    | cons b m => b = a \/ In a m
    end.

  Fixpoint concat (l : list (list A)) : list A :=
    match l with
    | nil => nil
    | cons x l => x ++ concat l
    end.

  Definition hd (default : A) (l : list A) :=
    match l with
    | nil => default
    | cons x _ => x
    end.

  Axiom app_nil_r : forall (l : list A), app l nil = l.

  Axiom app_inj_tail :
    forall (x y : list A) (a b : A),
      app x (cons a nil) = app y (cons b nil) -> x = y /\ a = b.
End Lists.

Section Fold_Left_Recursor.
  Context [A B : Type].
  Variable f : A -> B -> A.
  Fixpoint fold_left (l:list B) (a0:A) : A :=
    match l with
    | nil => a0
    | cons b t => fold_left t (f a0 b)
    end.
  Lemma fold_left_app : forall (l l':list B)(i:A),
    fold_left (l++l') i = fold_left l' (fold_left l i).
  Proof.
    now intro l; induction l; cbn.
  Qed.
End Fold_Left_Recursor.

Section Fold_Right_Recursor.
  Context [A B : Type].
  Variable f : B -> A -> A.
  Variable a0 : A.
  Fixpoint fold_right (l : list B) : A :=
    match l with
    | nil => a0
    | cons b t => f b (fold_right t)
    end.
End Fold_Right_Recursor.

Section Map.
  Context [A B : Type].
  Variable f : A -> B.

  Fixpoint map (l : list A) : list B :=
    match l with
    | nil => nil
    | cons a t => (f a) :: (map t)
    end.
  Lemma in_map :
    forall (l:list A) (x:A), In x l -> In (f x) (map l).
  Proof.
    intro l; induction l; firstorder (subst; auto).
  Qed.
End Map.

Section FlatMap.
  Context [A B : Type].
  Variable f : A -> list B.

  Fixpoint flat_map (l : list A) : list B :=
    match l with
    | nil => nil
    | cons x t => app (f x) (flat_map t)
    end.
End FlatMap.

Section Elts.
  Context [A : Type].

  Fixpoint nth (n : nat) (l : list A) (default : A) {struct l} : A :=
    match n, l with
    | O, cons x l' => x
    | O, nil => default
    | S m, nil => default
    | S m, cons x t => nth m t default
    end.
End Elts.

Section Cutting.
  Context [A : Type].

  Fixpoint skipn (n : nat)(l : list A) : list A :=
    match n with
    | 0 => l
    | S n =>
        match l with
        | nil => nil
        | cons a l => skipn n l
        end
    end.
End Cutting.

Module ListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..))
  (format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]") : list_scope.
Open Scope list_scope.
End ListNotations.
