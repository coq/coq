From Corelib Require Export Morphisms Setoid .

Class Equiv A := equiv: relation A.

Infix "≡" := equiv (at level 70, no associativity).
Infix "≡@{ A }" := (@equiv A _)
  (at level 70, only parsing, no associativity).

Notation "(≡)" := equiv (only parsing).

(** Unbundled version *)
Class Dist A := dist : nat -> relation A.

Notation "x ≡{ n }≡ y" := (dist n x y)
  (at level 70, n at next level, format "x  ≡{ n }≡  y").
Notation "x ≡{ n }@{ A }≡ y" := (dist (A:=A) n x y)
  (at level 70, n at next level, only parsing).

Notation NonExpansive f := (forall n, Proper (dist n ==> dist n ==> dist n) f).

Record OfeMixin A `{Equiv A, Dist A} := {
  mixin_equiv_dist (x y : A) : x ≡ y <-> forall n, x ≡{n}≡ y;
}.

(** Bundled version *)
Structure ofeT := OfeT {
  ofe_car :> Type;
  ofe_equiv : Equiv ofe_car;
  ofe_dist : Dist ofe_car;
  ofe_mixin : OfeMixin ofe_car
}.
#[export] Hint Extern 0 (Equiv _) => eapply (@ofe_equiv _) : typeclass_instances.
#[export] Hint Extern 0 (Dist _) => eapply (@ofe_dist _) : typeclass_instances.

(** Lifting properties from the mixin *)
Section ofe_mixin.
  Context {A : ofeT}.
  Implicit Types x y : A.
  Lemma equiv_dist x y : x ≡ y <-> forall n, x ≡{n}≡ y.
  Proof. apply (mixin_equiv_dist _ (ofe_mixin A)). Qed.
End ofe_mixin.

Axiom _0 : Prop. (* dummy which somehow bothers mangle names *)
Set Mangle Names.

(** General properties *)
Section ofe.
  Context {A : ofeT}.

  Lemma ne_proper_2 {B C : ofeT} (f : A -> B -> C) `{Hf:!NonExpansive f} :
    Proper ((≡) ==> (≡) ==> (≡)) f.
  Proof.
    unfold Proper, respectful.
    setoid_rewrite equiv_dist.
    intros.
    apply Hf;auto.
  Qed.
End ofe.
