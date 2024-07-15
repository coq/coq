Unset Elimination Schemes.
Inductive eq (A:Type) (x:A) : A -> Prop :=
    eq_refl : x = x :>A

where "x = y :> A" := (@ eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
Notation "x <> y" := (x <> y :>_) : type_scope.

Arguments eq {A} x _.
Arguments eq_refl {A x} , [A] x.
Set Elimination Schemes.

Scheme eq_rect := Minimality for eq Sort Type.
Scheme eq_rec := Minimality for eq Sort Set.
Scheme eq_ind := Minimality for eq Sort Prop.

(* needed for discriminate to recognize the hypothesis *)
Register eq as core.eq.type.
Register eq_refl as core.eq.refl.
Register eq_ind as core.eq.ind.
Register eq_rect as core.eq.rect.

Lemma foo (H : true = false) : False.
Proof.
  discriminate.
Defined.
Print foo.

Goal False.
  let c := eval cbv delta [foo] in foo in
    match c with
      context[eq_ind] => idtac
    end.
Abort.
