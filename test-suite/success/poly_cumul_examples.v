Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Universes.

Module Commands.
  Section poly.
    Universe i j k.

    Constraint i < max (j, k).

    Fail Check Constraint max(j, k) < i.
    Check Constraint i < max(j, k).

    Constraint i < j.
    Check Constraint i+1 <= j.
    Fail Check Constraint i < k.

    Definition foo@{} : Type@{max (j + 1, k + 1)} := Type@{i}.

  End poly.
End Commands.

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

End IsTrunc_inference.
