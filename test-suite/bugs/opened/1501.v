Set Implicit Arguments.


Require Export Relation_Definitions.
Require Export Setoid.


Section Essais.

(* Parametrized Setoid *)
Parameter K : Type -> Type.
Parameter equiv : forall A : Type, K A -> K A -> Prop.
Parameter equiv_refl : forall (A : Type) (x : K A), equiv x x.
Parameter equiv_sym : forall (A : Type) (x y : K A), equiv x y -> equiv y x.
Parameter equiv_trans : forall (A : Type) (x y z : K A), equiv x y -> equiv y z
-> equiv x z.

(* basic operations *)
Parameter val : forall A : Type, A -> K A.
Parameter bind : forall A B : Type, K A -> (A -> K B) -> K B.

Parameter
  bind_compat :
    forall (A B : Type) (m1 m2 : K A) (f1 f2 : A -> K B),
    equiv m1 m2 ->
    (forall x : A, equiv (f1 x) (f2 x)) -> equiv (bind m1 f1) (bind m2 f2).

(* monad axioms *)
Parameter
  bind_val_l :
    forall (A B : Type) (a : A) (f : A -> K B), equiv (bind (val a) f) (f a).
Parameter
  bind_val_r :
    forall (A : Type) (m : K A), equiv (bind m (fun a => val a)) m.
Parameter
  bind_assoc :
    forall (A B C : Type) (m : K A) (f : A -> K B) (g : B -> K C),
    equiv (bind (bind m f) g) (bind m (fun a => bind (f a) g)).


Hint Resolve equiv_refl equiv_sym equiv_trans: monad.

Instance equiv_rel A: Equivalence (@equiv A).
Proof.
 constructor.
 intros xa; apply equiv_refl.
 intros xa xb; apply equiv_sym.
 intros xa xb xc; apply equiv_trans.
Defined.

Definition fequiv (A B: Type)  (f g: A -> K B) := forall (x:A), (equiv (f x) (g
x)).

Lemma fequiv_refl : forall (A B: Type) (f : A -> K B), fequiv f f.
Proof.
  unfold fequiv; auto with monad.
Qed.

Lemma fequiv_sym : forall (A B: Type) (x y : A -> K B), fequiv x y -> fequiv y
x.
Proof.
  unfold fequiv; auto with monad.
Qed.

Lemma fequiv_trans : forall (A B: Type) (x y z : A -> K B), fequiv x y ->
fequiv
y z -> fequiv x z.
Proof.
  unfold fequiv; intros; eapply equiv_trans; auto with monad.
Qed.

Instance fequiv_re A B: Equivalence (@fequiv A B).
Proof.
 constructor.
 intros f; apply fequiv_refl.
 intros f g; apply fequiv_sym.
 intros f g h; apply fequiv_trans.
Defined.

Instance bind_mor A B: Morphisms.Proper (@equiv _ ==> @fequiv _ _ ==> @equiv _) (@bind A B).
Proof.
 unfold fequiv; intros x y xy_equiv f g fg_equiv; apply bind_compat; auto.
Qed.

Lemma test:
  forall (A B: Type) (m1 m2 m3: K A) (f: A -> A -> K B),
 (equiv m1 m2) -> (equiv m2 m3) ->
   equiv (bind m1 (fun a => bind m2 (fun a' => f a a')))
         (bind m2 (fun a => bind m3 (fun a' => f a a'))).
Proof.
  intros A B m1 m2 m3 f H1 H2.
  setoid_rewrite H1. (* this works *)
  Fail setoid_rewrite H2.
Abort.
(*  trivial by equiv_refl.
Qed.*)
