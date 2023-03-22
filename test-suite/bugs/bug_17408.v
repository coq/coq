Record CRing : Type := { cr_crr : Type; }.

Axiom cpoly : CRing -> Type.
Definition cpoly_cring CR : CRing := Build_CRing (cpoly CR).

Axiom cpoly_induc : forall (CR : CRing) (P : cr_crr (cpoly_cring CR) -> Prop), forall (p : cr_crr (cpoly_cring CR)), P p.

Goal forall CR (a : cr_crr (cpoly_cring CR)), a = a.
Proof.
(* Dubious behaviour of the scheme recognition algorithm. It realizes that
   cpoly_induc looks like a scheme, but it considers CR to be a parameter,
   despite the type of the argument not being some constant applied to it. *)
induction a using cpoly_induc.
Qed.
