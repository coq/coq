Definition idw (A : Type) := A.
Lemma foobar : unit.
Proof.
  Require Import Program.
  apply (const tt tt).
Qed.

Lemma foobar' : unit.
  Lemma aux : forall A : Type, A -> unit.
  Proof. intros. pose (foo := idw A). exact tt. Show Universes. Qed.
  apply (@aux unit tt).
Qed.

Set Printing Universes.

Module Mono.

Inductive myeq (A : Type) (a : A) : A -> Prop :=
  myeq_refl : myeq A a a.
Arguments myeq {A}.

Infix "==" := myeq (at level 89).

Module Int.

  (** Internal side-effect *)
  Lemma foo (x y : nat) : x == y -> x == y.
  Proof.
    intros H.
    rewrite H.
    apply myeq_refl.
  Qed.
End Int.

Module Nested.

  (** Internal side-effect by nested lemma, whose universe is used in the following proof *)
  Lemma bar : Type.
  Proof.
    
    Lemma internal : Type.
      exact Type.
    Qed.
          
    apply internal.
  Qed.
  (* internal and bar are globally defined *)
End Nested.

Module NestedDef.

  (** Internal side-effect by nested lemma, whose universe is used in the following proof *)
  Lemma bar : Type.
  Proof.
    
    Lemma internal : Type.
      exact Type.
    Qed.
          
    apply internal.
  Defined.
  
End NestedDef.

End Mono.


Module Poly.

Set Universe Polymorphism.
  
Inductive myeq@{i} (A : Type@{i}) (a : A) : A -> Type@{i} :=
  myeq_refl : myeq A a a.
Arguments myeq {A}.

Infix "==" := myeq (at level 89).

Module Int.

  (** Internal side-effect *)
  Lemma foo (x y : nat) : x == y -> x == y.
  Proof.
    intros H.
    rewrite H.
    apply myeq_refl.
  Qed.


  Check internal_myeq_rew_r@{_ _}.
  Check foo@{}.
  (** The nested lemma is polymorphic, foo has no universes *)
End Int.

Module Nested.

  (** Internal side-effect by nested lemma, whose universe is used in the following proof *)
  Lemma bar : Type.
  Proof.
    
    Lemma internal : Type.
      exact Type.
    Qed.
          
    apply internal.
  Qed.
  (* internal and bar are globally defined *)
  Check internal@{_ _}.

  (** bar has three, it instantiates the two of internal *)
  Check bar@{_ _ _}.
    
End Nested.

Module NestedDef.

  (** Internal side-effect by nested lemma, whose universe is used in the following proof *)
  Lemma bar : Type.
  Proof.
    
    Lemma internal : Type.
      exact Type.
    Qed.
          
    apply internal.
  Defined.
  (* internal and bar are globally defined *)
  Check internal@{_ _}.

  (** bar has three, it instantiates the two of internal *)
  Check bar@{_ _ _}.
  
End NestedDef.

End Poly.

