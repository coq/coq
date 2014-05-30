Module withoutpoly.

Inductive empty :=. 

Inductive emptyt : Type :=. 
Inductive singleton : Type :=
  single.
Inductive singletoninfo : Type :=
  singleinfo : unit -> singletoninfo.
Inductive singletonset : Set :=
  singleset.

Inductive singletonnoninfo : Type :=
  singlenoninfo : empty -> singletonnoninfo.

Inductive singletoninfononinfo : Prop :=
  singleinfononinfo : unit -> singletoninfononinfo.

Inductive bool : Type := 
  | true | false.

Inductive smashedbool : Prop := 
  | trueP | falseP.
End withoutpoly.

Set Universe Polymorphism.

Inductive empty :=. 
Inductive emptyt : Type :=. 
Inductive singleton : Type :=
  single.
Inductive singletoninfo : Type :=
  singleinfo : unit -> singletoninfo.
Inductive singletonset : Set :=
  singleset.

Inductive singletonnoninfo : Type :=
  singlenoninfo : empty -> singletonnoninfo.

Inductive singletoninfononinfo : Prop :=
  singleinfononinfo : unit -> singletoninfononinfo.

Inductive bool : Type := 
  | true | false.

Inductive smashedbool : Prop := 
  | trueP | falseP.

Section foo.
  Let T := Type.
  Inductive polybool : T := 
  | trueT | falseT.
End foo.

Inductive list (A: Type) : Type := 
| nil : list A
| cons : A -> list A -> list A.

Module ftypSetSet.
Inductive ftyp : Type :=
  | Funit : ftyp 
  | Ffun : list ftyp -> ftyp 
  | Fref : area -> ftyp
with area : Type := 
  | Stored : ftyp -> area        
.
End ftypSetSet.


Module ftypSetProp.
Inductive ftyp : Type :=
  | Funit : ftyp 
  | Ffun : list ftyp -> ftyp 
  | Fref : area -> ftyp
with area : Type := 
  | Stored : (* ftyp ->  *)area        
.
End ftypSetProp.

Module ftypSetSetForced.
Inductive ftyp : Type :=
  | Funit : ftyp 
  | Ffun : list ftyp -> ftyp 
  | Fref : area -> ftyp
with area : Set (* Type *) := 
  | Stored : (* ftyp ->  *)area        
.
End ftypSetSetForced.

Unset Universe Polymorphism.

Set Printing Universes.  
Module Easy.

  Polymorphic Inductive prod (A : Type) (B : Type) : Type :=
    pair : A -> B -> prod A B.
  
  Check prod nat nat.
  Print Universes.


  Polymorphic Inductive sum (A B:Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.
  Print sum.
  Check (sum nat nat).

End Easy.

Section Hierarchy.

Definition Type3 := Type.
Definition Type2 := Type : Type3.
Definition Type1 := Type : Type2.

Definition id1 := ((forall A : Type1, A) : Type2).
Definition id2 := ((forall A : Type2, A) : Type3).
Definition id1' := ((forall A : Type1, A) : Type3).
Fail Definition id1impred := ((forall A : Type1, A) : Type1).

End Hierarchy.

Section structures.

Record hypo : Type := mkhypo {
   hypo_type : Type;
   hypo_proof : hypo_type
 }.

Definition typehypo (A : Type) : hypo := {| hypo_proof := A |}.

Polymorphic Record dyn : Type := 
  mkdyn {
      dyn_type : Type;
      dyn_proof : dyn_type
    }.

Definition monotypedyn (A : Type) : dyn := {| dyn_proof := A |}.
Polymorphic Definition typedyn (A : Type) : dyn := {| dyn_proof := A |}.

Definition atypedyn : dyn := typedyn Type.

Definition projdyn := dyn_type atypedyn.

Definition nested := {| dyn_type := dyn; dyn_proof := atypedyn |}.

Definition nested2 := {| dyn_type := dyn; dyn_proof := nested |}.

Definition projnested2 := dyn_type nested2.

Polymorphic Definition nest (d : dyn) := {| dyn_proof := d |}.

Polymorphic Definition twoprojs (d : dyn) := dyn_proof d = dyn_proof d.

End structures.

Section cats.
  Local Set Universe Polymorphism.
  Require Import Utf8.
  Definition fibration (A : Type) := A -> Type.
  Definition Hom (A : Type) := A -> A -> Type.

  Record sigma (A : Type) (P : fibration A) :=
    { proj1 : A; proj2 : P proj1} .

  Class Identity {A} (M : Hom A) :=
    identity : ∀ x, M x x.
  
  Class Inverse {A} (M : Hom A) :=
    inverse : ∀ x y:A, M x y -> M y x.
  
  Class Composition {A} (M : Hom A) :=
    composition : ∀ {x y z:A}, M x y -> M y z -> M x z.
  
  Notation  "g ° f" := (composition f g) (at level 50). 
  
  Class Equivalence T (Eq : Hom T):= 
    {
      Equivalence_Identity :> Identity Eq ;
      Equivalence_Inverse :> Inverse Eq ;
      Equivalence_Composition :> Composition Eq 
    }.

  Class EquivalenceType (T : Type) : Type := 
    {
      m2: Hom T;
      equiv_struct :> Equivalence T m2 }.
  
  Polymorphic Record cat (T : Type) := 
    { cat_hom : Hom T;
      cat_equiv : forall x y, EquivalenceType (cat_hom x y) }.

  Definition catType := sigma Type cat.

  Notation "[ T ]" := (proj1 T).

  Require Import Program.

  Program Definition small_cat : cat Empty_set :=
    {| cat_hom x y := unit |}.
  Next Obligation. 
    refine ({|m2:=fun x y => True|}). 
    constructor; red; intros; trivial.
  Defined.

  Record iso (T U : Set) := 
    { f : T -> U;
      g : U -> T }.

  Program Definition Set_cat : cat Set :=
    {| cat_hom := iso |}.
  Next Obligation. 
    refine ({|m2:=fun x y => True|}). 
    constructor; red; intros; trivial.
  Defined.

  Record isoT (T U : Type) := 
    { isoT_f : T -> U;
      isoT_g : U -> T }.

  Program Definition Type_cat : cat Type :=
    {| cat_hom := isoT |}.
  Next Obligation. 
    refine ({|m2:=fun x y => True|}). 
    constructor; red; intros; trivial.
  Defined.
    
  Polymorphic Record cat1 (T : Type) := 
    { cat1_car : Type;
      cat1_hom : Hom cat1_car;
      cat1_hom_cat : forall x y, cat (cat1_hom x y) }.
End cats.  

Polymorphic Definition id {A : Type} (a : A) : A := a.

Definition typeid := (@id Type).


Fail Check (Prop : Set).
Fail Check (Set : Set).
Check (Set : Type).
Check (Prop : Type).
Definition setType := $(let t := type of Set in exact t)$.

Definition foo (A : Prop) := A.

Fail Check foo Set.
Check fun A => foo A.
Fail Check fun A : Type => foo A.
Check fun A : Prop => foo A.
Fail Definition bar := fun A : Set => foo A.

Fail Check (let A := Type in foo (id A)).

Definition fooS (A : Set) := A.

Check (let A := nat in fooS (id A)).
Fail Check (let A := Set in fooS (id A)).
Fail Check (let A := Prop in fooS (id A)).

(* Some tests of sort-polymorphisme *)
Section S.
Polymorphic Variable A:Type.
(*
Definition f (B:Type) := (A * B)%type.
*)
Polymorphic Inductive I (B:Type) : Type := prod : A->B->I B.

Check I nat.

End S.
(*
Check f nat nat : Set.
*)
Definition foo' := I nat nat.
Print Universes. Print foo. Set Printing Universes. Print foo.

(* Polymorphic axioms: *)
Polymorphic Axiom funext : forall (A B : Type) (f g : A -> B), 
                 (forall x, f x = g x) -> f = g.

(* Check @funext. *)
(* Check funext. *)

Polymorphic Definition fun_ext (A B : Type) := 
  forall (f g : A -> B), 
    (forall x, f x = g x) -> f = g.

Polymorphic Class Funext A B := extensional : fun_ext A B.

Section foo2. 
  Context `{forall A B, Funext A B}.
  Print Universes.
End foo2.
