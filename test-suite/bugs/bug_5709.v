Set Primitive Projections.

Record ofeT := OfeT { ofe_car :> Type; }.

Unset Primitive Projections.

Axiom dist : forall {A}, A -> Prop.

Record cFunctor := CFunctor {
  cFunctor_car : ofeT -> ofeT;
  cFunctor_map : forall A : ofeT, cFunctor_car A;
}.

Definition iprod {A} (B : A -> ofeT) := forall x, B x.

Canonical Structure iprodC A (B : A -> ofeT) : ofeT := OfeT (iprod B).

Definition iprodC_map {A} {B : A -> ofeT} (f : forall x, B x) : iprodC A B := f.

Axiom iprodC_map_ne : forall {A} {B : A -> ofeT} x, dist (@iprodC_map A B x).

Definition iprodCF {C} (F : cFunctor) : cFunctor := {|
  cFunctor_car := fun B => iprodC C (fun c => cFunctor_car F B);
  cFunctor_map := fun B => iprodC_map (fun c => cFunctor_map F B)
|}.

Lemma iprodCF_contractive {C} (F : cFunctor) (B : ofeT) :
  dist (@cFunctor_map (@iprodCF C F) B).
Proof.
  apply iprodC_map_ne.
  (* Anomaly "Uncaught exception Retyping.RetypeError(4)." Please report at http://coq.inria.fr/bugs/. *)
Qed.
