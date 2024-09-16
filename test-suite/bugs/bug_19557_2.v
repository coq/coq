
Definition not (A : Type) := A -> False.

Record HProp := {
  hprop_type : Type ;
}.

Coercion hprop_type : HProp >-> Sortclass.

Definition merely (A : Type) : HProp.
Admitted.

Section SwapTypes.

  Context (A B : Type).

  Lemma foo X (p:merely (X = B)) :
    sigT (fun p0 : not (merely (X = A)) => merely (X = B)).
    refine (existT _ (fun q => _) p).
  Abort.
End SwapTypes.
