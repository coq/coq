(* Bug report #2830 (evar defined twice) covers different bugs *)

(* 1- This was submitted by qb.h.agws *)

Module A.

Set Implicit Arguments.

Inductive Bit := O | I.

Inductive BitString: nat -> Set :=
| bit: Bit -> BitString 0
| bitStr: forall n: nat, Bit -> BitString n -> BitString (S n).

Definition BitOr (a b: Bit) :=
  match a, b with
  | O, O => O
  | _, _ => I
  end.

(* Should fail with an error; used to failed in 8.4 and trunk with
   anomaly Evd.define: cannot define an evar twice *)

Fail Fixpoint StringOr (n m: nat) (a: BitString n) (b: BitString m) :=
  match a with
  | bit a' =>
      match b with
      | bit b' => bit (BitOr a' b')
      | bitStr b' bT => bitStr b' (StringOr (bit a') bT)
      end
  | bitStr a' aT =>
      match b with
      | bit b' => bitStr a' (StringOr aT (bit b'))
      | bitStr b' bT => bitStr (BitOr a' b') (StringOr aT bT)
      end
  end.

End A.

(* 2- This was submitted by Andrew Appel *)

Module B.

Require Import Program Relations.

Record ageable_facts (A:Type) (level: A -> nat) (age1:A -> option A)  :=
{ af_unage : forall x x' y', level x' = level y' -> age1 x = Some x' -> exists y, age1 y = Some y'
; af_level1 : forall x, age1 x = None <-> level x = 0
; af_level2 : forall x y, age1 x = Some y -> level x = S (level y)
}.

Arguments af_unage {A level age1}.
Arguments af_level1 {A level age1}.
Arguments af_level2 {A level age1}.

Class ageable (A:Type) := mkAgeable
{ level : A -> nat
; age1 : A -> option A
; age_facts : ageable_facts A level age1
}.
Definition age {A} `{ageable A} (x y:A) := age1 x = Some y.
Definition necR   {A} `{ageable A} : relation A := clos_refl_trans A age.
Delimit Scope pred with pred.
Local Open Scope pred.

Definition hereditary {A} (R:A->A->Prop) (p:A->Prop) :=
  forall a a':A, R a a' -> p a -> p a'.

Definition pred (A:Type) {AG:ageable A} :=
  { p:A -> Prop | hereditary age p }.

Bind Scope pred with pred.

Definition app_pred {A} `{ageable A} (p:pred A) : A -> Prop := proj1_sig p.
Definition pred_hereditary `{ageable} (p:pred A) := proj2_sig p.
Coercion app_pred : pred >-> Funclass.
Global Opaque pred.

Definition derives {A} `{ageable A} (P Q:pred A) := forall a:A, P a -> Q a.
Arguments derives : default implicits.

Program Definition andp {A} `{ageable A} (P Q:pred A) : pred A :=
   fun a:A => P a /\ Q a.
Next Obligation.
  intros; intro; intuition;  apply pred_hereditary with a; auto.
Qed.

Program Definition imp {A} `{ageable A} (P Q:pred A) : pred A :=
   fun a:A => forall a':A, necR a a' -> P a' -> Q a'.
Next Obligation.
  intros; intro; intuition.
  apply H1; auto.
  apply rt_trans with a'; auto.
  apply rt_step; auto.
Qed.

Program Definition allp {A} `{ageable A} {B: Type} (f: B -> pred A) : pred A
  := fun a => forall b, f b a.
Next Obligation.
  intros; intro; intuition.
  apply pred_hereditary with a; auto.
  apply H1.
Qed.

Notation "P '<-->' Q" := (andp (imp P Q) (imp Q P)) (at level 57, no associativity) : pred.
Notation "P '|--' Q" := (derives P Q) (at level 80, no associativity).
Notation "'All'  x ':' T  ',' P " := (allp (fun x:T => P%pred)) (at level 65, x at level 99) : pred.

Lemma forall_pred_ext  {A} `{agA : ageable A}: forall B P Q,
 (All x : B, (P x <--> Q x)) |-- (All x : B, P x) <--> (All x: B, Q x).
Abort.

End B.

(* 3. *)

(* This was submitted by Anthony Cowley *)

Require Import Coq.Classes.Morphisms.
Require Import Setoid.

Module C.

Reserved Notation "a ~> b" (at level 70, right associativity).
Reserved Notation "a ≈ b" (at level 54).
Reserved Notation "a ∘ b" (at level 50, left associativity).
Generalizable All Variables.

Class Category (Object:Type) (Hom:Object -> Object -> Type) := {
    hom := Hom where "a ~> b" := (hom a b) : category_scope
  ; ob := Object
  ; id : forall a, hom a a
  ; comp : forall c b a, hom b c -> hom a b -> hom a c
    where "g ∘ f" := (comp _ _ _ g f)  : category_scope
  ; eqv : forall a b, hom a b -> hom a b -> Prop
    where "f ≈ g" := (eqv _ _ f g) : category_scope
  ; eqv_equivalence : forall a b, Equivalence (eqv a b)
  ; comp_respects : forall a b c,
    Proper (eqv b c ==> eqv a b ==> eqv a c) (comp c b a)
  ; left_identity : forall `(f:a ~> b), id b ∘ f ≈ f
  ; right_identity : forall `(f:a ~> b), f ∘ id a ≈ f
  ; associativity : forall `(f:a~>b) `(g:b~>c) `(h:c~>d),
    h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f
}.
Notation "a ~> b" := (@hom _ _ _ a b) : category_scope.
Notation "g ∘ f" := (@comp _ _ _ _ _ _ g f) : category_scope.
Notation "a ≈ b" := (@eqv _ _ _ _ _ a b) : category_scope.
Notation "a ~{ C }~> b" := (@hom _ _ C a b) (at level 100) : category_scope.
Coercion ob : Category >-> Sortclass.

Open Scope category_scope.

Add Parametric Relation `(C:Category Ob Hom) (a b : Ob) : (hom a b) (eqv a b)
  reflexivity proved by (@Equivalence_Reflexive _ _ (eqv_equivalence a b))
  symmetry proved by (@Equivalence_Symmetric _ _ (eqv_equivalence a b))
  transitivity proved by (@Equivalence_Transitive _ _ (eqv_equivalence a b))
  as parametric_relation_eqv.

Add Parametric Morphism `(C:Category Ob Hom) (c b a : Ob) : (comp c b a)
  with signature (eqv _ _ ==> eqv _ _ ==> eqv _ _) as parametric_morphism_comp.
  intros x y Heq x' y'. apply comp_respects. exact Heq.
  Defined.

Class Functor `(C:Category) `(D:Category) (im : C -> D) := {
  functor_im := im
  ; fmap : forall {a b}, `(a ~> b) -> im a ~> im b
  ; fmap_respects : forall a b (f f' : a ~> b), f ≈ f' -> fmap f ≈ fmap f'
  ; fmap_preserves_id : forall a, fmap (id a) ≈ id (im a)
  ; fmap_preserves_comp : forall `(f:a~>b) `(g:b~>c), 
    fmap g ∘ fmap f ≈ fmap (g ∘ f)
}.
Coercion functor_im : Functor >-> Funclass.
Arguments fmap [Object Hom C Object0 Hom0 D im] _ [a b].

Add Parametric Morphism `(C:Category) `(D:Category)
  (Im:C->D) (F:Functor C D Im) (a b:C) : (@fmap _ _ C _ _ D Im F a b)
  with signature (@eqv C _ C a b ==> @eqv D _ D (Im a) (Im b)) 
  as parametric_morphism_fmap.
intros. apply fmap_respects. assumption. Qed.

(* HERE IS THE PROBLEMATIC INSTANCE. If we change this to a regular Definition,
   then the problem goes away. *)
Instance functor_comp `{C:Category} `{D:Category} `{E:Category} 
  {Gim} (G:Functor D E Gim) {Fim} (F:Functor C D Fim)
  : Functor C E (Basics.compose Gim Fim).
intros. apply Build_Functor with (fmap := fun a b f => fmap G (fmap F f)).
abstract (intros; rewrite H; reflexivity).
abstract (intros; repeat (rewrite fmap_preserves_id); reflexivity).
abstract (intros; repeat (rewrite fmap_preserves_comp); reflexivity).
Defined.

Definition skel {A:Type} : relation A := @eq A.
Instance skel_equiv A : Equivalence (@skel A).
Admitted.

Import FunctionalExtensionality.
Instance set_cat : Category Type (fun A B => A -> B) := {
  id := fun A => fun x => x
  ; comp c b a f g := fun x => f (g x)
  ; eqv := fun A B => @skel (A -> B)
}.
intros. compute. symmetry. apply eta_expansion.
intros. compute. symmetry. apply eta_expansion.
intros. compute. reflexivity. Defined.

(* The [list] type constructor is a Functor. *)

Import List.

Definition setList (A:set_cat) := list A.
Instance list_functor : Functor set_cat set_cat setList.
apply Build_Functor with (fmap := @map).
intros. rewrite H. reflexivity.
intros; simpl; apply functional_extensionality. 
  induction x; [auto|simpl]. rewrite IHx. reflexivity.
intros; simpl; apply functional_extensionality.
  induction x; [auto|simpl]. rewrite IHx. reflexivity.
Defined.

Local Notation "[ a , .. , b ]" := (a :: .. (b :: nil) ..) : list_scope.
Definition setFmap {Fim} {F:Functor set_cat set_cat Fim} `(f:A~>B) (xs:Fim A) := fmap F f xs.

(* We want to infer the [Functor] instance based on the value's
   structure, but the [functor_comp] instance throws things awry. *)
Eval cbv in setFmap (fun x => x * 3) [67,8].

End C.
