Axiom _0: Prop.

From Stdlib Require Export Morphisms Setoid.

Class Equiv A := equiv: relation A.

Reserved Notation "P ⊢ Q" (at level 99, Q at level 200, right associativity).
Reserved Notation "P ⊣⊢ Q" (at level 95, no associativity).
Reserved Notation "■ P" (at level 20, right associativity).

(** Define the scope *)
Declare Scope bi_scope.
Delimit Scope bi_scope with I.

Structure bi :=
  Bi { bi_car :> Type;
       bi_entails : bi_car -> bi_car -> Prop;
       bi_impl : bi_car -> bi_car -> bi_car;
       bi_forall : forall A, (A -> bi_car) -> bi_car; }.

#[export] Declare Instance bi_equiv `{PROP:bi} : Equiv (bi_car PROP).

Arguments bi_car : simpl never.
Arguments bi_entails {PROP} _%_I _%_I : simpl never, rename.
Arguments bi_impl {PROP} _%_I _%_I : simpl never, rename.
Arguments bi_forall {PROP _} _%_I : simpl never, rename.

Notation "P ⊢ Q" := (bi_entails P%I Q%I) .
Notation "P ⊣⊢ Q" := (equiv (A:=bi_car _) P%I Q%I) .

Infix "->" := bi_impl : bi_scope.
Reserved Notation "∀ x .. y , P"
  (at level 10, x binder, y binder, P at level 200,
  format "'[  ' '[  ' ∀  x  ..  y ']' ,  '/' P ']'").
Notation "∀ x .. y , P" :=
  (bi_forall (fun x => .. (bi_forall (fun y => P)) ..)%I) : bi_scope.

(* bug disappears if definitional class *)
Class Plainly (PROP : bi) := { plainly : PROP -> PROP; }.
Notation "■ P" := (plainly P) : bi_scope.

Section S.
  Context {I : Type} {PROP : bi} `(Plainly PROP).

  Lemma plainly_forall `{Plainly PROP} {A} (Ψ : A -> PROP) : (∀ a, ■ (Ψ a)) ⊣⊢ ■ (∀ a, Ψ a).
  Proof. Admitted.

  Global Instance entails_proper :
    Proper (equiv ==> equiv ==> iff) (bi_entails : relation PROP).
  Proof. Admitted.

  Global Instance impl_proper :
    Proper (equiv ==> equiv ==> equiv) (@bi_impl PROP).
  Proof. Admitted.

  Global Instance forall_proper A :
    Proper (pointwise_relation _ equiv ==> equiv) (@bi_forall PROP A).
  Proof. Admitted.

  Declare Instance PROP_Equivalence: Equivalence (@equiv PROP _).

  Set Mangle Names.
  Lemma foo (P : I -> PROP) K:
    K ⊢ ∀ (j : I)
          (_ : Prop) (* bug disappears if this is removed *)
      , (∀ i0, ■ P i0) -> P j.
  Proof.
    setoid_rewrite plainly_forall.
    (* retype in case the tactic did some nonsense *)
    match goal with |- ?T => let _ := type of T in idtac end.
  Abort.
End S.
