Set Printing Universes.

Module AutoYes.
  Inductive Box (A:Type) : Type := box : A -> Box A.

  About Box.

  (* This checks that Box is template poly, see module No for how it fails *)
  Universe i j. Constraint i < j.
  Definition j_lebox (A:Type@{j}) := Box A.
  Definition box_lti A := Box A : Type@{i}.

End AutoYes.

Module AutoNo.
  Unset Auto Template Polymorphism.
  Inductive Box (A:Type) : Type := box : A -> Box A.

  About Box.

  Universe i j. Constraint i < j.
  Definition j_lebox (A:Type@{j}) := Box A.
  Fail Definition box_lti A := Box A : Type@{i}.

End AutoNo.

Module Yes.
  #[universes(template)]
  Inductive Box@{i} (A:Type@{i}) : Type@{i} := box : A -> Box A.

  About Box.

  Universe i j. Constraint i < j.
  Definition j_lebox (A:Type@{j}) := Box A.
  Definition box_lti A := Box A : Type@{i}.

End Yes.

Module No.
  #[universes(template=no)]
  Inductive Box (A:Type) : Type := box : A -> Box A.

  About Box.

  Universe i j. Constraint i < j.
  Definition j_lebox (A:Type@{j}) := Box A.
  Fail Definition box_lti A := Box A : Type@{i}.
End No.

Module ExplicitTemplate.
  #[universes(template)]
  Inductive identity@{i} (A : Type@{i}) (a : A) : A -> Type@{i} := id_refl (_:A) : identity A a a.

  (* There used to be a weird interaction of template polymorphism and inductive
     types which fall in Prop due to kernel sort inference. This inductive is
     template polymorphic, but the universe annotation Type@{i} was ignored by
     the kernel which infered it lived in any universe and thus put it in Prop.
     This is not the case anymore since return sort inference has been removed
     from the kernel. Now the universe annotation is respected by the kernel. *)
  Fail Check (identity Type nat nat : Prop).
  Check (identity True I I : Prop).
  Check identity nat 0 0 : Set.
  Fail Check identity Type nat nat : Set.
  Check identity Type nat nat : Type.
End ExplicitTemplate.

Module ExplicitTemplate2.
  #[universes(template)]
  Inductive identity@{i} (A : Type@{i}) (a : A) : A -> Type@{i} := id_refl : identity A a a.
  (* we generate fresh qualities for A and the conclusion, and they end up unrelated
     therefore the conclusion quality has no binders,
     we can't make it a template poly quality and instead collapse to Type *)

  Fail Check (identity Type nat nat : Prop).
  Fail Check (identity True I I : Prop).
  Check identity nat 0 0 : Set.
  Fail Check identity Type nat nat : Set.
  Check identity Type nat nat : Type.
End ExplicitTemplate2.

Polymorphic Definition f@{i} : Type@{i} := nat.
Polymorphic Definition baz@{i} : Type@{i} -> Type@{i} := fun x => x.

Section Foo.
  Universe u.
  Context (A : Type@{u}).

  Inductive Bar :=
  | bar : A -> Bar.

  Set Universe Minimization ToSet.
  Inductive Baz :=
  | cbaz : A -> baz Baz -> Baz.

  Inductive Baz' :=
  | cbaz' : A -> baz@{Set} nat -> Baz'.

  (* 2 constructors, at least in Set *)
  Inductive Bazset@{v} :=
  | cbaz1 : A -> baz@{v} Bazset -> Bazset
  | cbaz2 : Bazset.

  Eval compute in ltac:(let T := type of A in exact T).

  Inductive Foo : Type :=
  | foo : A -> f -> Foo.

End Foo.

Set Printing Universes.
(* Cannot fall back to Prop or Set anymore as baz is no longer template-polymorphic *)
Fail Check Bar True : Prop.
Fail Check Bar nat : Set.
About Baz.

Check cbaz True I.

(** Neither can it be Set *)
Fail Check Baz nat : Set.

(** No longer possible for Baz' which contains a type in Set *)
Fail Check Baz' True : Prop.
Fail Check Baz' nat : Set.

Fail Check Bazset True : Prop.
Fail Check Bazset True : Set.

(** We can force the universe instantiated in [baz Bazset] to be [u], so Bazset lives in max(Set, u). *)
Constraint u = Bazset.v.
(** As u is global it is already > Set, so: *)
Definition bazsetex@{i | i < u} : Type@{u} := Bazset Type@{i}.

(* Bazset is closed for universes u = u0, cannot be instantiated with Prop *)
Definition bazseetpar (X : Type@{u}) : Type@{u} := Bazset X.

(** Would otherwise break singleton elimination and extraction. *)
Fail Check Foo True : Prop.
Fail Check Foo True : Set.

Definition foo_proj {A} (f : Foo A) : nat :=
  match f with foo _ _ n => n end.

Definition ex : Foo True := foo _ I 0.
Check foo_proj ex.

(** See failure/Template.v for a test of the unsafe Unset Template Check usage *)

Module AutoTemplateTest.
Set Warnings "+auto-template".
Section Foo.
  Universe u'.
  Context (A : Type@{u'}).

  (* Not failing as Bar cannot be made template polymorphic at all *)
  Inductive Bar :=
  | bar : A -> Bar.
End Foo.
End AutoTemplateTest.

Module TestTemplateAttribute.
  Section Foo.
    Universe u.
    Context (A : Type@{u}).

    Set Warnings "+no-template-universe".

    (* Failing as Bar cannot be made template polymorphic at all *)
    Fail #[universes(template)] Inductive Bar :=
    | bar : A -> Bar.

  End Foo.
End TestTemplateAttribute.

Module SharingWithoutSection.
Inductive Foo A (S:= fun _ => Set : ltac:(let ty := type of A in exact ty))
  := foo : S A -> Foo A.
Fail Check Foo True : Prop.
End SharingWithoutSection.

Module OkNotCovered.
(* Here it happens that box is safe but we don't see it *)
Section S.
Universe u.
Variable A : Type@{u}.
Inductive box (A:Type@{u}) := Box : A -> box A.
Definition B := Set : Type@{u}.
End S.
Fail Check box True : Prop.
End OkNotCovered.

Module BoxBox.

  Inductive Box (A:Type) := box (_:A).
  Inductive Box' (A:Type) := box' (_:Box A).
  Check Box' True : Prop.

End BoxBox.

Module TemplateUnit.

Set Warnings "-no-template-universe".

(* This is marked as template without any actual template universe. *)
#[universes(template)] Inductive foo := Foo.

Check (foo : Prop).

End TemplateUnit.

Module TemplateParamUnit.

(* template where the univ doesn't appear in the conclusion (here Prop) *)
Set Warnings "+no-template-universe".
Inductive foo (A : Type) := Foo.

Polymorphic Definition foo'@{u|} (A:Type@{u}) : Prop := foo A.

Check (foo unit : Prop).

End TemplateParamUnit.

Module TemplateAlg.

  Inductive foo (A:Type) (B :Type) := C (_:A).

  Check foo True nat : Prop.

  Check fun A => foo A nat : Prop.
  Fail Check fun A:Set => foo A nat : Prop.

  Goal Prop.
    let c := constr:(forall A, prod A A) in
    exact c.
  Defined.

  Universes u v.

  Axiom U : Type@{u}.
  Axiom V : Type@{v}.

  Check foo (U * V) True : Type@{max(u,v)}.

End TemplateAlg.

Module TemplateNoExtraCsts.

  Polymorphic Definition opt'@{u|} (A:Type@{u}) := option A.
  Polymorphic Definition some@{u|} (A:Type@{u}) (x:A) : opt' A := Some x.

End TemplateNoExtraCsts.

Module BoundedQuality.
  Inductive dumb' (b:bool) (B : Type) := cons' : B -> (b = true -> dumb' false nat) -> dumb' b B.

  (* dumb' true _ contains a nat *)
  Fail Check dumb' true True : Prop.

  Check dumb' true nat : Set.
  Fail Check dumb' true Set : Set.
  Check dumb' true Set.
End BoundedQuality.

Module BoundedQuality2.
  Inductive dumb' (A:Type) (b:bool) (B : Type) := cons' : A -> (b = true -> dumb' A false nat) -> dumb' A b B.

  Check dumb' True true Set : Prop.
  Fail Check dumb' nat true Set : Prop.
  Check dumb' nat true Set : Set.
  Fail Check dumb' Set true Set : Set.
  Check dumb' Set true Set.
End BoundedQuality2.

Module UnminimizedOption.
  Unset Universe Minimization ToSet.
  Inductive option A := None | Some (_:A).

  Fail Check option True : Prop.
  Check option nat : Set.
  Fail Check option Set : Set.
  Check option Set : Type.
End UnminimizedOption.

Module UnminimizedFunction.
  Unset Universe Minimization ToSet.
  Inductive Foo (T:Type) := foo (_:nat -> T).

  Check Foo True : Prop.
  Fail Check Foo nat : Prop.
  Check Foo nat : Set.
  Fail Check Foo Set : Set.
  Check Foo Set : Type.
End UnminimizedFunction.

Module ExplicitOption.
  Inductive option@{u} (A:Type@{u}) : Type@{u} := None | Some (_:A).

  Fail Check option True : Prop.
  Check option nat : Set.
  Fail Check option Set : Set.
  Check option Set : Type.
End ExplicitOption.

Module QvarInCtor.
  (* this could be sort polymorphic:
  Record Foo@{q|u v|} (A:Type@{q|u}) : Type@{q|max(u,v+1)}
    := { foo1 : A; foo2 : forall P : Type@{q|v}, P }.

  but qvar "q" (and univ "v") cannot be template poly due to appearing in the constructor
  (even if we generalized template poly to allow conversion-irrelevant appearances,
  this one isn't irrelevant)

  so we need to collapse q := Type and can be template poly on u *)
  Record Foo A := { foo1 : A ; foo2 : forall P, P }.

  Fail Check Foo True : Prop.
  Fail Check Foo nat : Set.
  Polymorphic Definition test@{|} : Type@{Foo.u1+1} := Foo nat.
  Polymorphic Definition test'@{u|} (A:Type@{u}) : Type@{max(u,Foo.u1+1)} := Foo A.
End QvarInCtor.

Module SemiPoly.
  Universe u.

  (* u cannot be template poly (it's global) but we could be template sort polymorphic *)
  Inductive foo (A:Type@{u}) (B:Type@{u}) C := pair (_:A) (_:B) (_:C).

  Fail Check foo True True True : Prop. (* maybe will be allowed someday *)
  Fail Check foo nat nat nat : Set. (* must not be allowed *)
End SemiPoly.
