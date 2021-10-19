(* Simple let-patterns *)
Variable A B : Type.

Definition l1 (t : A * B * B) : A := let '(x, y, z) := t in x.
Print l1.
Definition l2 (t : (A * B) * B) : A := let '((x, y), z) := t in x.
Definition l3 (t : A * (B * B)) : A := let '(x, (y, z)) := t in x.
Print l3.

Record someT (A : Type) := mkT { a : nat; b: A }.

Definition l4 A (t : someT A) : nat := let 'mkT _ x y := t in x.
Print l4.
Print sigT.

Definition l5 A (B : A -> Type) (t : sigT B) : B (projT1 t) :=
  let 'existT _ x y := t return B (projT1 t) in y.

Definition l6 A (B : A -> Type) (t : sigT B) : B (projT1 t) :=
  let 'existT _ x y as t' := t return B (projT1 t') in y.

Definition l7 A (B : A -> Type) (t : sigT B) : B (projT1 t) :=
  let 'existT _ x y as t' in sigT _ := t return B (projT1 t') in y.

Definition l8 A (B : A -> Type) (t : sigT B) : B (projT1 t) :=
  match t with
    existT _ x y => y
  end.

(** An example from algebra, using let' and inference of return clauses
   to deconstruct contexts. *)

Record a_category (A : Type) (hom : A -> A -> Type) := {  }.

Definition category := { A : Type & { hom : A -> A -> Type & a_category A hom } }.

Record a_functor (A : Type) (hom : A -> A -> Type) (C : a_category A hom) := {  }.

Notation " x :& y " := (@existT _ _ x y) (right associativity, at level 55) : core_scope.

Definition functor (c d : category) :=
  let ' A :& homA :& CA := c in
  let ' B :& homB :& CB := d in
    A -> B.

Definition identity_functor (c : category) : functor c c :=
  let 'A :& homA :& CA := c in
    fun x => x.

Definition functor_composition (a b c : category) : functor a b -> functor b c -> functor a c :=
  let 'A :& homA :& CA := a in
  let 'B :& homB :& CB := b in
  let 'C :& homB :& CB := c in
    fun f g =>
      fun x => g (f x).

Module Inference.

Check fun '(x,y) => (eq_refl x,eq_refl y).
Check fun '((x,y):nat*bool) => (eq_refl x,eq_refl y).
Check fun '(existT _ x y) => (eq_refl x,eq_refl y).

Check fun '((x,y),(z,w)) => (eq_refl x,eq_refl y,eq_refl z,eq_refl w).
Check fun '(existT _ x (existT _ z w)) => (eq_refl x,eq_refl z,eq_refl w).
Check fun '(existT _ (existT _ x y) w) => (eq_refl x,eq_refl y,eq_refl w).

(* Unfortunately this still fails due to limits in solving *)
Fail Check fun '(existT _ (existT _ x y) (existT _ z w)) => (eq_refl x,eq_refl y,eq_refl z,eq_refl w).

Record sigT (A : Type) (P : A -> Type) : Type := { projT1 : A ; projT2 : P projT1 }.
Check fun '{| projT1 := x; projT2 := y |} => (eq_refl x,eq_refl y).

Set Primitive Projections.

Record sigT' (A : Type) (P : A -> Type) : Type := { projT1' : A ; projT2' : P projT1' }.
Check fun '{| projT1' := x; projT2' := y |} => (eq_refl x,eq_refl y).

End Inference.
