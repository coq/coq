Require Import TestSuite.admit.
Set Implicit Arguments.
Set Universe Polymorphism.
Generalizable All Variables.

Record Category (obj : Type) := { Morphism : obj -> obj -> Type }.

Definition SetCat : @Category Set := @Build_Category Set (fun s d => s -> d).

Record Foo := { foo : forall A (f : Morphism SetCat A A), True }.

Local Notation PartialBuild_Foo pf := (@Build_Foo (fun A f => pf A f)).

Set Printing Universes.
Let SetCatFoo' : Foo.
  let pf := fresh in
  let pfT := fresh in
  evar (pfT : Prop);
    cut pfT;
    [ subst pfT; intro pf;
      let t := constr:(PartialBuild_Foo pf) in
      let t' := (eval simpl in t) in
      exact t'
    | ].
  admit.
(* Toplevel input, characters 15-20:
Error: Universe inconsistency (cannot enforce Set <= Prop).
 *)
