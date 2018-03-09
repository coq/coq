Polymorphic Cumulative Inductive T1 := t1 : T1.
Fail Monomorphic Cumulative Inductive T2 := t2 : T2.

Polymorphic Cumulative Record R1 := { r1 : T1 }.
Fail Monomorphic Cumulative Inductive R2 := {r2 : T1}.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Universes.

Inductive List (A: Type) := nil | cons : A -> List A -> List A.

Definition LiftL@{k i j|k <= i, k <= j} {A:Type@{k}} : List@{i} A -> List@{j} A := fun x => x.

Lemma LiftL_Lem A (l : List A) : l = LiftL l.
Proof. reflexivity. Qed.

Inductive Tp := tp : Type -> Tp.

Definition LiftTp@{i j|i <= j} : Tp@{i} -> Tp@{j} := fun x => x.

Fail Definition LowerTp@{i j|j < i} : Tp@{i} -> Tp@{j} := fun x => x.

Record Tp' := { tp' : Tp }.

Definition CTp := Tp.
(* here we have to reduce a constant to infer the correct subtyping. *)
Record Tp'' := { tp'' : CTp }.

Definition LiftTp'@{i j|i <= j} : Tp'@{i} -> Tp'@{j} := fun x => x.
Definition LiftTp''@{i j|i <= j} : Tp''@{i} -> Tp''@{j} := fun x => x.

Lemma LiftC_Lem (t : Tp) : LiftTp t = t.
Proof. reflexivity. Qed.

Section subtyping_test.
  Universe i j.
  Constraint i < j.

  Inductive TP2 := tp2 : Type@{i} -> Type@{j} -> TP2.

End subtyping_test.

Record A : Type := { a :> Type; }.

Record B (X : A) : Type := { b : X; }.

NonCumulative Inductive NCList (A: Type)
  := ncnil | nccons : A -> NCList A -> NCList A.

Fail Definition LiftNCL@{k i j|k <= i, k <= j} {A:Type@{k}}
  : NCList@{i} A -> NCList@{j} A := fun x => x.

Inductive eq@{i} {A : Type@{i}} (x : A) : A -> Type@{i} := eq_refl : eq x x.

Definition funext_type@{a b e} (A : Type@{a}) (B : A -> Type@{b})
  := forall f g : (forall a, B a),
    (forall x, eq@{e} (f x) (g x))
    -> eq@{e} f g.

Section down.
  Universes a b e e'.
  Constraint e' < e.
  Lemma funext_down {A B}
    : @funext_type@{a b e} A B -> @funext_type@{a b e'} A B.
  Proof.
    intros H f g Hfg. exact (H f g Hfg).
  Defined.
End down.

Record Arrow@{i j} := { arrow : Type@{i} -> Type@{j} }.

Fail Definition arrow_lift@{i i' j j' | i' < i, j < j'}
  : Arrow@{i j} -> Arrow@{i' j'}
  := fun x => x.

Definition arrow_lift@{i i' j j' | i' = i, j <= j'}
  : Arrow@{i j} -> Arrow@{i' j'}
  := fun x => x.

Inductive Mut1 A :=
| Base1 : Type -> Mut1 A
| Node1 : (A -> Mut2 A) -> Mut1 A
with Mut2 A :=
     | Base2 : Type -> Mut2 A
     | Node2 : Mut1 A -> Mut2 A.

(* If we don't reduce T while inferring cumulativity for the
   constructor we will see a Rel and believe i is irrelevant. *)
Inductive withparams@{i j} (T:=Type@{i}:Type@{j}) := mkwithparams : T -> withparams.

Definition withparams_co@{i i' j|i < i', i' < j} : withparams@{i j} -> withparams@{i' j}
  := fun x => x.

Fail Definition withparams_not_irr@{i i' j|i' < i, i' < j} : withparams@{i j} -> withparams@{i' j}
  := fun x => x.

(** Cumulative constructors *)


Record twotys@{u v w} : Type@{w} :=
  twoconstr { fstty : Type@{u}; sndty : Type@{v} }.

Monomorphic Universes i j k l.

Monomorphic Constraint i < j.
Monomorphic Constraint j < k.
Monomorphic Constraint k < l.

Parameter Tyi : Type@{i}.

Definition checkcumul :=
  eq_refl _ : @eq twotys@{k k l} (twoconstr@{i j k} Tyi Tyi) (twoconstr@{j i k} Tyi Tyi).

(* They can only be compared at the highest type *)
Fail Definition checkcumul' :=
  eq_refl _ : @eq twotys@{i k l} (twoconstr@{i j k} Tyi Tyi) (twoconstr@{j i k} Tyi Tyi).

(* An inductive type with an irrelevant universe *)
Inductive foo@{i} : Type@{i} := mkfoo { }.

Definition bar := foo.

(* The universe on mkfoo is flexible and should be unified with i. *)
Definition foo1@{i} : foo@{i} := let x := mkfoo in x. (* fast path for conversion *)
Definition foo2@{i} : bar@{i} := let x := mkfoo in x. (* must reduce *)

(* Rigid universes however should not be unified unnecessarily. *)
Definition foo3@{i j|} : foo@{i} := let x := mkfoo@{j} in x.
Definition foo4@{i j|} : bar@{i} := let x := mkfoo@{j} in x.

(* Constructors for an inductive with indices *)
Module WithIndex.
  Inductive foo@{i} : (Prop -> Prop) -> Prop := mkfoo: foo (fun x => x).

  Monomorphic Universes i j.
  Monomorphic Constraint i < j.
  Definition bar : eq mkfoo@{i} mkfoo@{j} := eq_refl _.
End WithIndex.
