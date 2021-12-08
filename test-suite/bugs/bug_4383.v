Definition resp {A B} (R:A->A->Prop) (R':B->B->Prop) (f g : A -> B)
:= forall x y, R x y -> R' (f x) (g y).
Definition restr {A} P R (x y : A) := (P x /\ P y) /\ R x y .
Definition func {A} (P:A -> Prop) F := A -> F .

Lemma foo {A B} {P:A->Prop} {R1} {R2:B->B->Prop} {f g}
(E : resp (restr P R1) R2 f g) x : P x -> R1 x x -> R2 (f x) (g x).
Proof. firstorder. Qed.

Section sec.
Context A (P:A->Prop) (R1:A->A->Prop).
Context B (R2:B->B->Prop).
Context (f g : func P B).

Definition R' := resp (restr P R1) R2.

Context (E: R' f g) (x:A).

Goal True.
pose proof foo E x.
Abort.

Typeclasses Opaque func.

Goal True.
pose proof foo E x.
(* Used to be: Unable to unify "R2 (f x0) (g y)" with
"?R2 (?f x0) (?g y)". *)
pose proof foo (f:=f) (g:=g) E x.
Abort.
End sec.
