Module Foo. 
  Inductive True2:Prop:= I2: (False->True2)->True2.

  Axiom Heq: (False->True2)=True2.
  
  Fail Fixpoint con (x:True2) :False :=
    match x with
        I2 f => con (match Heq with @eq_refl _ _ => f end)
    end.
End Foo.

Require Import ClassicalFacts.

Inductive True1 : Prop := I1 : True1
with True2 : Prop := I2 : True1 -> True2.

Section func_unit_discr.

Hypothesis Heq : True1 = True2.

Fail Fixpoint contradiction (u : True2) : False :=
contradiction (
    match u with
      | I2 Tr =>
         match Heq in (_ = T) return T with
         | eq_refl => Tr
         end
    end).

End func_unit_discr.

Require Import Vectors.VectorDef.

About caseS.
About tl.
Open Scope vector_scope.
Local Notation "[]" := (@nil _).
Local Notation "h :: t" := (@cons _ h _ t) (at level 60, right associativity).
Definition is_nil {A n} (v : t A n) : bool := match v with [] => true | _ => false end.

Fixpoint id {A n} (v : t A n) : t A n :=
  match v in t _ n' return t A n' with
    | (h :: t) as v' => h :: id (tl v')
    |_ => []
  end.
