(* An example involving a first-order unification triggering a cyclic constraint *)

Module A.
Notation "{ x : A | P }" := (sigT (fun x:A => P)).
Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Open Scope fibration_scope.
Notation "p @ q" := (eq_trans p q) (at level 20).
Notation "p ^" := (eq_sym p) (at level 3).
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) 
: P y :=
  match p with eq_refl => u end.
Notation "p # x" := (transport _ p x) (right associativity, at level 65, only 
parsing).
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with eq_refl => eq_refl end.
Definition apD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x=y): p # (f 
x) = f y
  := match p with eq_refl => eq_refl end.
Axiom transport_compose
  : forall {A B} {x y : A} (P : B -> Type) (f : A -> B) (p : x = y) (z : P (f 
x)),
    transport (fun x => P (f x)) p z  =  transport P (ap f p) z.
Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope object_scope with object.
Record PreCategory := { object :> Type ; morphism : object -> object -> Type }.
Delimit Scope functor_scope with functor.
Record Functor (C D : PreCategory) :=
  { object_of :> C -> D;
    morphism_of : forall s d, morphism C s d -> morphism D (object_of s) 
(object_of d) }.
Arguments object_of {C%category D%category} f%functor c%object : rename, simpl 
nomatch.
Arguments morphism_of [C%category] [D%category] f%functor [s%object d%object] 
m%morphism : rename, simpl nomatch.
Section path_functor.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Local Notation path_functor'_T F G
    := { HO : object_of F = object_of G
       | transport (fun GO => forall s d, morphism C s d -> morphism D (GO s) 
(GO d))
                   HO
                   (morphism_of F)
         = morphism_of G }
         (only parsing).
  Definition path_functor'_sig_inv (F G : Functor C D) : F = G -> 
path_functor'_T F G
    := fun H'
       => (ap object_of H';
             (transport_compose _ object_of _ _) ^ @ apD (@morphism_of _ _) H').

End path_functor.
End A.

(* A variant of it with more axioms *)

Module B.
Notation "{ x : A | P }" := (sigT (fun x:A => P)).
Notation "( x ; y )" := (existT _ x y).
Notation "p @ q" := (eq_trans p q) (at level 20).
Notation "p ^" := (eq_sym p) (at level 3).
Axiom transport : forall {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x), P y.
Notation "p # x" := (transport _ p x) (right associativity, at level 65, only 
parsing).
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with eq_refl => eq_refl end.
Axiom apD : forall {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x=y), p # (f 
x) = f y.
Axiom transport_compose
  : forall {A B} {x y : A} (P : B -> Type) (f : A -> B) (p : x = y) (z : P (f 
x)),
    transport (fun x => P (f x)) p z  =  transport P (ap f p) z.
Record PreCategory := { object :> Type ; morphism : object -> object -> Type }.
Record Functor (C D : PreCategory) :=
  { object_of :> C -> D;
    morphism_of : forall s d, morphism C s d -> morphism D (object_of s) 
(object_of d) }.
Arguments object_of {C D} f c : rename, simpl nomatch.
Arguments morphism_of [C] [D] f [s d] m : rename, simpl nomatch.
Section path_functor.
  Variable C D : PreCategory.
  Local Notation path_functor'_T F G
    := { HO : object_of F = object_of G
       | transport (fun GO => forall s d, morphism C s d -> morphism D (GO s) 
(GO d))
                   HO
                   (morphism_of F)
         = morphism_of G }.
  Definition path_functor'_sig_inv (F G : Functor C D) : F = G -> 
path_functor'_T F G
    := fun H'
       => (ap object_of H';
             (transport_compose _ object_of _ _) ^ @ apD (@morphism_of _ _) H').

End path_functor.
End B.
