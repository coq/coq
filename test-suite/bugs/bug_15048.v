

Reserved Notation "x = y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x = y" (at level 70, no associativity).

Reserved Notation "x + y" (at level 50, left associativity).

Reserved Notation "n .+1" (at level 2, left associativity, format "n .+1").
Reserved Notation "n .+2" (at level 2, left associativity, format "n .+2").
Reserved Notation "g 'o' f" (at level 40, left associativity).
Reserved Notation "! x" (at level 3, format "'!' x").
Declare Scope path_scope.
Delimit Scope type_scope with type.
Delimit Scope trunc_scope with trunc.

Global Open Scope trunc_scope.
Global Open Scope path_scope.
Global Open Scope type_scope.

Global Set Universe Polymorphism.

Notation "A -> B" := (forall (_ : A), B) : type_scope.


Create HintDb typeclass_instances discriminated.

Definition Relation (A : Type) := A -> A -> Type.

Class Symmetric {A} (R : Relation A) :=
  symmetry : forall x y, R x y -> R y x.

Notation Type0 := Set.

Cumulative Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.

Global Instance symmetric_paths {A} : Symmetric (@paths A) | 0 := @inverse A.

Notation "1" := idpath : path_scope.

Class Contr_internal (A : Type) := Build_Contr {
  center : A ;
  contr : (forall y : A, center = y)
}.

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Bind Scope trunc_scope with trunc_index.

Notation "n .+1" := (trunc_S n) : trunc_scope.
Notation "n .+2" := (n.+1.+1)%trunc : trunc_scope.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | minus_two => Contr_internal A
    | n'.+1 => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.

Notation Contr := (IsTrunc minus_two).
Notation IsHSet := (IsTrunc minus_two.+2).

Inductive Empty : Type0 := .

Inductive Unit : Type0 := tt : Unit.
Module Export Core.
Set Implicit Arguments.

Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope object_scope with object.

Record PreCategory :=
  Build_PreCategory' {
      object :> Type;
      morphism : object -> object -> Type;

      identity : forall x, morphism x x;
      compose : forall s d d',
                  morphism d d'
                  -> morphism s d
                  -> morphism s d'
                              where "f 'o' g" := (compose f g);

      associativity : forall x1 x2 x3 x4
                             (m1 : morphism x1 x2)
                             (m2 : morphism x2 x3)
                             (m3 : morphism x3 x4),
                        (m3 o m2) o m1 = m3 o (m2 o m1);

      associativity_sym : forall x1 x2 x3 x4
                                 (m1 : morphism x1 x2)
                                 (m2 : morphism x2 x3)
                                 (m3 : morphism x3 x4),
                            m3 o (m2 o m1) = (m3 o m2) o m1;

      left_identity : forall a b (f : morphism a b), identity b o f = f;
      right_identity : forall a b (f : morphism a b), f o identity a = f;

      identity_identity : forall x, identity x o identity x = identity x;

      trunc_morphism : forall s d, IsHSet (morphism s d)
    }.

Bind Scope category_scope with PreCategory.
Arguments identity {!C%_category} / x%_object : rename.
Arguments compose {!C%_category} / {s d d'}%_object (m1 m2)%_morphism : rename.

Infix "o" := compose : morphism_scope.

End Core.
Delimit Scope functor_scope with functor.

Local Open Scope morphism_scope.

Section Functor.
  Variables C D : PreCategory.

  Record Functor :=
    {
      object_of :> C -> D;
      morphism_of : forall s d, morphism C s d
                                -> morphism D (object_of s) (object_of d);
      composition_of : forall s d d'
                              (m1 : morphism C s d) (m2: morphism C d d'),
                         morphism_of _ _ (m2 o m1)
                         = (morphism_of _ _ m2) o (morphism_of _ _ m1);
      identity_of : forall x, morphism_of _ _ (identity x)
                              = identity (object_of x)
    }.
End Functor.

Generalizable Variables A B m n f.

Fixpoint trunc_index_inc (k : trunc_index) (n : nat)
  : trunc_index
  := match n with
      | O => k
      | S m => (trunc_index_inc k m).+1
    end.

Definition nat_to_trunc_index (n : nat) : trunc_index
  := (trunc_index_inc minus_two n).+2.

Definition int_to_trunc_index (v : Decimal.int) : option trunc_index
  := match v with
     | Decimal.Pos d => Some (nat_to_trunc_index (Nat.of_uint d))
     | Decimal.Neg d => match Nat.of_uint d with
                        | 2%nat => Some minus_two
                        | 1%nat => Some (minus_two.+1)
                        | 0 => Some (minus_two.+2)
                        | _ => None
                        end
     end.

Definition num_int_to_trunc_index v : option trunc_index :=
  match Nat.of_num_int v with
  | Some n => Some (nat_to_trunc_index n)
  | None => None
  end.

Fixpoint trunc_index_to_little_uint n acc :=
  match n with
  | minus_two => acc
  | minus_two.+1 => acc
  | minus_two.+2 => acc
  | trunc_S n => trunc_index_to_little_uint n (Decimal.Little.succ acc)
  end.

Definition trunc_index_to_int n :=
  match n with
  | minus_two => Decimal.Neg (Nat.to_uint 2)
  | minus_two.+1 => Decimal.Neg (Nat.to_uint 1)
  | n => Decimal.Pos (Decimal.rev (trunc_index_to_little_uint n Decimal.zero))
  end.

Definition trunc_index_to_num_int n :=
  Number.IntDecimal (trunc_index_to_int n).


Global Instance istrunc_succ `{IsTrunc n A}
  : IsTrunc n.+1 A | 1000.
Admitted.

Global Instance contr_unit : Contr Unit | 0 := let x := {|
  center := tt;
  contr := fun t : Unit => match t with tt => 1 end
|} in x.

Definition groupoid_category X `{IsTrunc (trunc_S (trunc_S (trunc_S minus_two))) X} : PreCategory.
Admitted.
  Definition discrete_category X `{IsHSet X} := groupoid_category X.
  Section indiscrete_category.

    Variable X : Type.

    Definition indiscrete_category : PreCategory
      := @Build_PreCategory' X
                             (fun _ _ => Unit)
                             (fun _ => tt)
                             (fun _ _ _ _ _ => tt)
                             (fun _ _ _ _ _ _ _ => idpath)
                             (fun _ _ _ _ _ _ _ => idpath)
                             (fun _ _ f => match f with tt => idpath end)
                             (fun _ _ f => match f with tt => idpath end)
                             (fun _ => idpath)
                             _.
  End indiscrete_category.
Local Open Scope nat_scope.

  Fixpoint CardinalityRepresentative (n : nat) : Type0 :=
    match n with
      | 0 => Empty
      | 1 => Unit
      | S n' => (CardinalityRepresentative n' + Unit)%type
    end.

  Coercion CardinalityRepresentative : nat >-> Sortclass.

  Global Instance trunc_cardinality_representative (n : nat)
  : IsHSet (CardinalityRepresentative n).
Admitted.

  Definition nat_category (n : nat) :=
    match n with
      | 0 => indiscrete_category 0
      | 1 => indiscrete_category 1
      | S (S n') => discrete_category (S (S n'))
    end.
    Notation "1" := (nat_category 1) : category_scope.
Notation terminal_category := (nat_category 1) (only parsing).

Class IsTerminalCategory (C : PreCategory)
      `{Contr (object C)}
      `{forall s d, Contr (morphism C s d)} := {}.
Global Instance: IsTerminalCategory 1 | 0 := {}.
Generalizable All Variables.

Section functors.
  Variable C : PreCategory.

  Definition from_terminal `{@IsTerminalCategory one Hone Hone'} (c : C)
  : Functor one C
    := Build_Functor
         one C
         (fun _ => c)
         (fun _ _ _ => identity c)
         (fun _ _ _ _ _ => symmetry _ _ (@identity_identity _ _))
         (fun _ => idpath).
End functors.

Local Notation "! x" := (@from_terminal _ terminal_category _ _ _ x) : functor_scope.

Definition CC_Functor' (C : PreCategory) (D : PreCategory) := Functor C D.

Coercion cc_functor_from_terminal' (C : PreCategory) (x : C) : CC_Functor' _ C
  := (!x)%functor.
