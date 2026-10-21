Polymorphic Cumulative Inductive T1 := t1 : T1.
Fail Monomorphic Cumulative Inductive T2 := t2 : T2.

Polymorphic Cumulative Record R1 := { r1 : T1 }.
Fail Monomorphic Cumulative Inductive R2 := {r2 : T1}.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Universes.

Inductive List (A: Type) := nil | cons : A -> List A -> List A.

Check eq_refl : List@{1} nat = List@{0} nat.

Definition LiftL@{k i j|k <= i, k <= j} {A:Type@{k}} : List@{i} A -> List@{j} A := fun x => x.

Lemma LiftL_Lem A (l : List A) : l = LiftL l.
Proof. reflexivity. Qed.

Inductive Tp := tp : Type -> Tp.

Definition LiftTp@{i j|i <= j} : Tp@{i} -> Tp@{j} := fun x => x.

Fail Definition LowerTp@{i j|j < i} : Tp@{i} -> Tp@{j} := fun x => x.

Record Tp' := { tp' : Tp }.

Definition CTp := Tp.
(* here we have to reduce a constant to infer the correct subtyping. *)
Record Tp''@{+u} := { tp'' : CTp@{u} }.

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

Definition arrow_lift@{i j j' | j < j'}
  : Arrow@{i j} -> Arrow@{i j'}
  := fun x => x.

Definition arrow_lift_inv@{i i' j j' | i' = i, j <= j'}
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
Definition foo2@{i} : bar := let x := mkfoo in x. (* must reduce *)

(* Rigid universes however should not be unified unnecessarily. *)
Definition foo3@{i j|} : foo@{i} := let x := mkfoo@{j} in x.
Definition foo4@{j|} : bar := let x := mkfoo@{j} in x.

(* Constructors for an inductive with indices *)
Module WithIndex.
  Inductive foo@{i} : (Prop -> Prop) -> Prop := mkfoo: foo (fun x => x).

  Monomorphic Universes i j.
  Monomorphic Constraint i < j.
  Definition bar : eq mkfoo@{i} mkfoo@{j} := eq_refl _.
End WithIndex.

Module CumulApp.

  (* i is covariant here, and we have one parameter *)
  Inductive foo@{i} (A : nat) : Type@{i+1} := mkfoo (B : Type@{i}).

  Definition bar@{i j|i<=j} := fun x : foo@{i} 0 => x : foo@{j} 0.

End CumulApp.

Module InSection.

Section S.
Polymorphic Cumulative Structure T : Type := {sort : Type}.
Polymorphic Universe u.
Polymorphic Cumulative Structure T' : Type := {sort' : Type -> Type@{u}}.
Polymorphic Cumulative Structure T'' : Type := {sort'' : Type}.
End S.

Check T@{Set}.
Check T'@{Set Set}.

(* T'' expects two universes, that is also u; do we really want it? *)
Fail Check T''@{Set}.

End InSection.

Module PolyList.

Inductive list@{i|} (A : Type@{i}) : Type@{i} :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} _ _.

Delimit Scope list_scope with list.
Bind Scope list_scope with list.

Notation "[ ]" := nil : list_scope.
Infix "::" := cons : list_scope.

Local Open Scope list_scope.

Fixpoint reverse_acc {A : Type} (acc : list A) (l : list A) : list A :=
  match l with
  | nil => acc
  | x :: l => reverse_acc (x :: acc) l
  end.

(** Reversing the order of a list. The list [ [a1; a2; ...; an] ] becomes [ [an; ...; a2; a1] ]. *)
Definition reverse {A : Type} (l : list A) : list A := reverse_acc nil l.

(** Descending sequence of natural numbers starting from [n.-1] to [0]. *)
Fixpoint seq_rev (n : nat) : list nat :=
    match n with
    | O => nil
    | S n => n :: seq_rev n
    end.

(** Ascending sequence of natural numbers [< n]. *)
Definition seq (n : nat) : list nat := reverse (seq_rev n).

Check seq@{}.
End PolyList.

Module IsTrunc_inference.
Local Unset Elimination Schemes.

Inductive trunc_index : Type@{0} :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Scheme trunc_index_ind := Induction for trunc_index Sort Type.
Scheme trunc_index_rec := Minimality for trunc_index Sort Type.

(* See comment above about the tactic [induction]. *)
Definition trunc_index_rect := trunc_index_ind.

(** We will use [Notation] for [trunc_index]es, so define a scope for them here. Numeral notation for [trunc_index]es is set up in Basics/Trunc.v. *)
Bind Scope trunc_scope with trunc_index.
Arguments trunc_S _%_trunc_scope.

Notation "n .+1" := (trunc_S n) : trunc_scope.
Local Open Scope trunc_scope.
Local Set Asymmetric Patterns.

Inductive paths@{i} {A : Type@{i}} (a : A) : A -> Type@{i} :=
  idpath : paths a a.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.
Class Contr_internal (A : Type) :=
  BuildContr {
      center : A ;
      contr : (forall y : A, center = y)
    }.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | minus_two => Contr_internal A
    | trunc_S n' => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Class IsTrunc (n : trunc_index) (A : Type) :=
  Trunc_is_trunc : IsTrunc_internal n A.

Definition unit_trunc := IsTrunc minus_two unit.
Check unit_trunc@{}.

Record TruncType (n : trunc_index) := {
  trunctype_type : Type ;
  trunctype_istrunc :: IsTrunc n trunctype_type
}.

Set Primitive Projections.

Record TruncType' (n : trunc_index) := {
  trunctype_type' : Type ;
  trunctype_istrunc' :: IsTrunc n trunctype_type'
}.

End IsTrunc_inference.

Module Decl.
  Definition foo@{i j| i < j + 1} : Type@{j+1} := Type@{i}.
  Definition foo'@{i j| i < j +} : Type@{j} := Type@{i}.
  Definition foo_ext@{i j| i < j+1} : Type@{j+1} := Type@{i}.
  Definition foo_ext'@{i j| i <= j +1 +} : Type@{j+1} := Type@{i}.
End Decl.
