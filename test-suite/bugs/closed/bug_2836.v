(* Check that possible instantiation made during evar materialization
   are taken into account and do not raise Not_found *)

Set Implicit Arguments.

Record SpecializedCategory (obj : Type) (Morphism : obj -> obj -> Type) := {
  Object :> _ := obj;

  Identity' : forall o, Morphism o o;
  Compose' : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d'
}.

Section SpecializedCategoryInterface.
  Variable obj : Type.
  Variable mor : obj -> obj -> Type.
  Variable C : @SpecializedCategory obj mor.

  Definition Morphism (s d : C) := mor s d.
  Definition Identity (o : C) : Morphism o o := C.(Identity') o.
  Definition Compose (s d d' : C) (m : Morphism d d') (m0 : Morphism s d) :
Morphism s d' := C.(Compose') s d d' m m0.
End SpecializedCategoryInterface.

Section ProductCategory.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.

(* Should fail nicely *)
Definition ProductCategory : @SpecializedCategory (objC * objD)%type (fun s d
=> (morC (fst s) (fst d) * morD (snd s) (snd d))%type).
Fail refine {|
      Identity' := (fun o => (Identity (fst o), Identity (snd o)));
      Compose' := (fun s d d' m2 m1 => (Compose (fst m2) (fst m1), Compose (snd
m2) (snd m1)))
    |}.
