
Notation "'∏'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).

Reserved Notation "X ≃ Y" (at level 80, no associativity).


Reserved Notation "g ∘ f"  (at level 40, left associativity).


Set Primitive Projections.

Record total2 { T: Type } ( P: T -> Type ) := tpair { pr1 : T; pr2 : P pr1 }.

Arguments tpair {_} _ _ _.
Arguments pr1 {_ _} _.
Arguments pr2 {_ _} _.

Notation "'∑'  x .. y , P" := (total2 (λ x, .. (total2 (λ y, P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.



Definition funcomp {X Y : Type} {Z:Y->Type} (f : X -> Y) (g : ∏ y:Y, Z y) := λ x, g (f x).

Declare Scope functions.

Open Scope functions.

Notation "g ∘ f" := (funcomp f g) : functions.

Definition isweq {X Y : Type} (f : X -> Y) : Type.
Admitted.

Definition weq (X Y : Type) : Type.
exact (∑ f:X->Y, isweq f).
Defined.

Notation "X ≃ Y" := (weq X%type Y%type) : type_scope.

Definition pr1weq {X Y : Type} := pr1 : X ≃ Y -> (X -> Y).
Coercion pr1weq : weq >-> Funclass.
Definition make_weq {X Y : Type} (f : X -> Y) (is: isweq f) : X ≃ Y.
exact (tpair (λ f : X -> Y, isweq f) f is).
Defined.

Theorem twooutof3c {X Y Z : Type} (f : X -> Y) (g : Y -> Z)
        (isf : isweq f) (isg : isweq g) : isweq (g ∘ f).
Admitted.
Definition weqcomp {X Y Z : Type} (w1 : X ≃ Y) (w2 : Y ≃ Z) : X ≃ Z.
exact (make_weq (λ (x : X), w2 (w1 x)) (twooutof3c w1 w2 (pr2 w1) (pr2 w2))).
Defined.


Delimit Scope weq_scope with weq.

Definition weqcomp_to_funcomp {X Y Z : Type} {f : X ≃ Y} {g : Y ≃ Z} :
  pr1weq (weqcomp f g) = pr1weq g ∘ pr1weq f.
Admitted.

Definition stn ( n : nat ) : Type.
Admitted.

Definition sequenceToFunction {X} (x:∑ n, stn n -> X) : stn (pr1 x) -> X.
Admitted.

Lemma foo
  M
  (I : Type)
  (m : I -> M)
  (n : nat)
  (x x' : stn n ≃ I)
  (K:stn n -> M) L Z
  :
  @eq (forall _ : stn n, M) Z
    (@sequenceToFunction M
       (@tpair nat (fun x0 : nat => forall _ : stn x0, M) n
          (fun z : stn n => K (@pr1weq I (stn n) L (@pr1weq (stn n) I x z)))))
.
Proof.
  Fail rewrite weqcomp_to_funcomp.
Abort.
