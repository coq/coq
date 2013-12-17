(* An example showing that prop-extensionality is incompatible with
   powerful extensions of the guard condition.
   Unlike the example in guard2, it is not exploiting the fact that
   the elimination of False always produces a subterm.

   Example due to Cristobal Camarero on Coq-Club.
   Adapted to nested types by Bruno Barras.
 *)

Axiom prop_ext: forall P Q, (P<->Q)->P=Q.

Module Unboxed.

Inductive True2:Prop:= I2: (False->True2)->True2.

Theorem Heq: (False->True2)=True2.
Proof.
apply prop_ext. split.
- intros. constructor. exact H.
- intros. exact H.
Qed.

Fail Fixpoint con (x:True2) :False :=
match x with
I2 f => con (match Heq in _=T return T with eq_refl => f end)
end.

End Unboxed.

(* This boxed example shows that it is not enough to just require
   that the return type of the match on Heq is an inductive type
 *)
Module Boxed.

Inductive box (T:Type) := Box (_:T).
Definition unbox {T} (b:box T) : T := let (x) := b in x.

Inductive True2:Prop:= I2: box(False->True2)->True2.

Definition Heq: (False->True2) <-> True2 :=
  conj (fun f => I2 (Box _ f)) (fun x _ => x).

Fail Fixpoint con (x:True2) :False :=
match x with
I2 f => con (unbox(match prop_ext _ _ Heq in _=T return box T with eq_refl => f end))
end.

End Boxed.
