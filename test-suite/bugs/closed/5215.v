Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Tactics.

Global Set Primitive Projections.

Global Set Universe Polymorphism.

Global Unset Universe Minimization ToSet.

Class Category : Type :=
{
  Obj : Type;
  Hom : Obj -> Obj -> Type;
  compose : forall {a b c : Obj}, (Hom a b) -> (Hom b c) -> (Hom a c);
  id : forall {a : Obj}, Hom a a;
}.

Arguments Obj {_}, _.
Arguments id {_ _}, {_} _, _ _.
Arguments Hom {_} _ _, _ _ _.
Arguments compose {_} {_ _ _} _ _, _ {_ _ _} _ _, _ _ _ _ _ _.

Coercion Obj : Category >-> Sortclass.

Definition Opposite (C : Category) : Category :=
{|

  Obj := Obj C;
  Hom := fun a b => Hom b a;
  compose :=
    fun a b c (f : Hom b a) (g : Hom c b) => compose C c b a g f;
  id := fun c => id C c;
|}.

Record Functor (C C' : Category) : Type :=
{
  FO : C -> C';
  FA : forall {a b}, Hom a b -> Hom (FO a) (FO b);
}.

Arguments FO {_ _} _ _.
Arguments FA {_ _} _ {_ _} _, {_ _} _ _ _ _.

Section Opposite_Functor.
  Context {C D : Category} (F : Functor C D).

  Program Definition Opposite_Functor : (Functor (Opposite C) (Opposite D)) :=
    {|
      FO := FO F;
      FA := fun _ _ h => FA F h;
    |}.

End Opposite_Functor.

Section Functor_Compose.
  Context {C C' C'' : Category} (F : Functor C C') (F' : Functor C' C'').

  Program Definition Functor_compose : Functor C C'' :=
    {|
      FO := fun c => FO F' (FO F c);
      FA := fun c d f => FA F' (FA F f)
    |}.

End Functor_Compose.

Section Algebras.
  Context {C : Category} (T : Functor C C).
  Record Algebra : Type :=
    {
      Alg_Carrier : C;
      Constructors : Hom (FO T Alg_Carrier) Alg_Carrier
    }.

  Record Algebra_Hom (alg alg' : Algebra) : Type :=
    {
      Alg_map : Hom (Alg_Carrier alg) (Alg_Carrier alg');

      Alg_map_com : compose (FA T Alg_map) (Constructors alg')
                     = compose (Constructors alg) Alg_map
    }.

  Arguments Alg_map {_ _} _.
  Arguments Alg_map_com {_ _} _.
  Program Definition Algebra_Hom_compose
          {alg alg' alg'' : Algebra}
          (h : Algebra_Hom alg alg')
          (h' : Algebra_Hom alg' alg'')
    : Algebra_Hom alg alg''
    :=
      {|
        Alg_map := compose (Alg_map h) (Alg_map h')
      |}.

  Next Obligation. Proof. Admitted.

  Lemma Algebra_Hom_eq_simplify (alg alg' : Algebra)
        (ah ah' : Algebra_Hom alg alg')
    : (Alg_map ah) = (Alg_map ah') -> ah = ah'.
  Proof. Admitted.

  Program Definition Algebra_Hom_id (alg : Algebra) : Algebra_Hom alg alg :=
    {|
      Alg_map := id
    |}.

  Next Obligation. Admitted.

  Definition Algebra_Cat : Category :=
    {|
      Obj := Algebra;
      Hom := Algebra_Hom;
      compose := @Algebra_Hom_compose;
      id := Algebra_Hom_id;
    |}.

End Algebras.

Arguments Alg_Carrier {_ _} _.
Arguments Constructors {_ _} _.
Arguments Algebra_Hom {_ _} _ _.
Arguments Alg_map {_ _ _ _} _.
Arguments Alg_map_com {_ _ _ _} _.
Arguments Algebra_Hom_id {_ _} _.

Section CoAlgebras.
  Context {C : Category}.

  Definition CoAlgebra (T : Functor C C) :=
    @Algebra (Opposite C) (Opposite_Functor T).

  Definition CoAlgebra_Hom {T : Functor C C} :=
      @Algebra_Hom (Opposite C) (Opposite_Functor T).

  Definition CoAlgebra_Hom_id {T : Functor C C} :=
    @Algebra_Hom_id  (Opposite C) (Opposite_Functor T).

  Definition CoAlgebra_Cat (T : Functor C C) :=
    @Algebra_Cat (Opposite C) (Opposite_Functor T).

End CoAlgebras.

Program Definition Type_Cat : Category :=
{|
  Obj := Type;
  Hom := (fun A B => A -> B);
  compose := fun A B C (g : A -> B) (h : B -> C) => fun (x : A) => h (g x);
  id := fun A => fun x => x
|}.

Local Obligation Tactic := idtac.

Program Definition Prod_Cat (C C' : Category) : Category :=
{|
  Obj := C * C';
  Hom :=
    fun a b =>
      ((Hom (fst a) (fst b)) * (Hom (snd a) (snd b)))%type;
  compose :=
    fun a b c f g =>
      ((compose (fst f) (fst g)), (compose (snd f)(snd g)));
  id := fun c => (id, id)
|}.

Class Terminal (C : Category) : Type :=
{
  terminal : C;
  t_morph : forall (d : Obj), Hom d terminal;
  t_morph_unique : forall (d : Obj) (f g : (Hom d terminal)), f = g
}.

Arguments terminal {_} _.
Arguments t_morph {_} _ _.
Arguments t_morph_unique {_} _ _ _ _.

Coercion terminal : Terminal >-> Obj.

Definition Initial (C : Category) := Terminal (Opposite C).
Existing Class Initial.

Record Product {C : Category} (c d : C) : Type :=
{
  product : C;
  Pi_1 : Hom product c;
  Pi_2 : Hom product d;
  Prod_morph_ex : forall (p' : Obj) (r1 : Hom p' c) (r2 : Hom p' d), (Hom p' product);
}.

Arguments Product _ _ _, {_} _ _.

Arguments Pi_1 {_ _ _ _}, {_ _ _} _.
Arguments Pi_2 {_ _ _ _}, {_ _ _} _.
Arguments Prod_morph_ex {_ _ _} _ _ _ _.

Coercion product : Product >-> Obj.

Definition Has_Products (C : Category) : Type := forall a b, Product a b.

Existing Class Has_Products.

Program Definition Prod_Func (C : Category) {HP : Has_Products C}
  : Functor (Prod_Cat C C) C :=
{|
  FO := fun x => HP (fst x) (snd x);
  FA := fun a b f => Prod_morph_ex _ _ (compose Pi_1 (fst f)) (compose  Pi_2 (snd f))
|}.

Arguments Prod_Func _ _, _ {_}.

Definition Sum (C : Category) := @Product (Opposite C).

Arguments Sum _ _ _, {_} _ _.

Definition Has_Sums (C : Category) : Type :=  forall (a b : C), (Sum a b).

Existing Class Has_Sums.

Program Definition sum_Sum (A B : Type) : (@Sum Type_Cat A B) :=
{|
  product := (A + B)%type;
  Prod_morph_ex :=
    fun (p' : Type)
        (r1 : A -> p')
        (r2 : B -> p')
        (X : A + B) =>
      match X return p' with
      | inl a => r1 a
      | inr b => r2 b
      end
|}.
Next Obligation. simpl; auto. Defined.
Next Obligation. simpl; auto. Defined.

Program Instance Type_Cat_Has_Sums : Has_Sums Type_Cat := sum_Sum.

Definition Sum_Func {C : Category} {HS : Has_Sums C} :
  Functor (Prod_Cat C C) C := Opposite_Functor (Prod_Func (Opposite C) HS).

Arguments Sum_Func _ _, _ {_}.

Program Instance unit_Type_term : Terminal Type_Cat :=
{
  terminal := unit;
  t_morph := fun _ _=> tt
}.

Next Obligation. Proof. Admitted.

Program Definition term_id : Functor Type_Cat (Prod_Cat Type_Cat Type_Cat) :=
{|
  FO := fun a => (@terminal Type_Cat _, a);
  FA := fun a b f => (@id _ (@terminal Type_Cat _), f)
|}.

Definition S_nat_func : Functor Type_Cat Type_Cat :=
  Functor_compose term_id (Sum_Func Type_Cat _).

Definition S_nat_alg_cat := Algebra_Cat S_nat_func.

CoInductive CoNat : Set :=
  | CoO : CoNat
  | CoS : CoNat -> CoNat
.

Definition S_nat_coalg_cat := @CoAlgebra_Cat Type_Cat S_nat_func.

Set Printing Universes.
Program Definition CoNat_alg_term : Initial S_nat_coalg_cat :=
{|
  terminal := _;
  t_morph := _
|}.

Next Obligation. Admitted.
Next Obligation. Admitted.

Axiom Admit : False.

Next Obligation.
Proof.
  intros d f g.
  assert(H1 := (@Alg_map_com _ _ _ _ f)). clear.
  assert (inl tt = inr tt) by (exfalso; apply Admit).
  discriminate.
  all: exfalso; apply Admit.
  Show Universes.
Qed.
