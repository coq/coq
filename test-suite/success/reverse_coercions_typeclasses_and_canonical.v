Set Primitive Projections.

Class IsPointed (A : Type) := point : A.

Record pType : Type := {
  pointed_type : Type ;
  ispointed_pointed_type : IsPointed pointed_type ;
}.
#[reversible]
Coercion pointed_type : pType >-> Sortclass.
Fail Canonical Build_pType.
Canonical Structure Build_pType' (A : Type) (a : IsPointed A) := Build_pType A a.

Axiom A : Type.
#[export]
Instance a : IsPointed A. Proof. Admitted.

Axiom lemma_about_ptype : forall (X : pType), Type.

Type (A : pType).
Type (lemma_about_ptype A).

(*
Ok, so here is what happens:
* you give `A : Type` where `?x : pType` is expected
* no coercion `Sortclass >-> pType` but (according to `Print Graph`) we have `[pointed_type] : pType ↣ Sortclass (reversible)`
* so reversible coercions look for `?x : pType` such that `pointed_type ?x = A`
* and canonical structure mechanism infers `?x = Build_pType' A _`
* finally, typeclass resolution fills the last `_` with `a`
*)
