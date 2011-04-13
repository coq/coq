(* Some tests of sort-polymorphisme *)
Section S.
Variable A:Type.
(*
Definition f (B:Type) := (A * B)%type.
*)
Inductive I (B:Type) : Type := prod : A->B->I B.
End S.
(*
Check f nat nat : Set.
*)
Check I nat nat : Set.

Definition I' (B : Type) := I B.

Check I' nat nat : Set.

Definition I'' (B : Type) := (I B B * I B B)%type.
Set Printing Universes.
Check I'' nat.
Definition id {A : Type} (a : A) := a.
Definition crelation (A:Type) := A -> A -> Type.
Print crelation.
Polymorphic Definition pcrelation (A:Type) := A -> A -> Type.
Print pcrelation.
Definition TYPE := Type.
Print TYPE.
Check crelation TYPE.
Check pcrelation TYPE.
Check pcrelation (pcrelation TYPE).

Definition foo := crelation TYPE.
Check crelation foo.

Class Category (obj : Type) (hom : crelation obj) := {
  id_obj o : hom o o ;
  comp {o o' o''} : hom o' o'' -> hom o o' -> hom o o''
}.
Class Functor {A H B H'} (C : Category A H) (D : Category B H') := {
  fmap : A -> B;
  fmap_F a b : H a b -> H' (fmap a) (fmap b)
}.


Instance TYPE_cat : Category TYPE (fun a b => a -> b) := 
  { id_obj o := id; comp o o' o'' g f := fun x => g (f x) }.

Instance ID_Functor {A H} (C : Category A H) : Functor C C := {
  fmap a := a ;
  fmap_F a b f := f }.


Record category := {
  obj : Type ; hom : crelation obj; cat : Category obj hom }.

Record functor (c d : category) := {
  funct : Functor (cat c) (cat d) }.

Instance functor_cat : Category category functor.
Proof. constructor. intros. constructor. apply (ID_Functor (cat o)).  admit.

Qed.

Class nat_trans {A H B H'} (C : Category A H) (D : Category B H') (F G : Functor C D) := {
  nat_transform o : H' (fmap (Functor:=F) o) (fmap (Functor:=G) o) ;
  nat_natural X Y (f : H X Y) : comp (nat_transform Y) (fmap_F (Functor:=F) _ _ f) =
  comp (fmap_F (Functor:=G) _ _ f) (nat_transform X)
}.

Record nat_transf {C D} (F G : functor C D) := {
  nat_transfo : nat_trans (cat C) (cat D) (funct _ _ F) (funct _ _ G) }.

Instance nat_trans_cat C D : Category (functor C D) (@nat_transf C D).
Proof. admit. Qed.


Polymorphic De
Print TYPE.
Check (id (A:=TYPE)).
Check (id (A:=Type)).
Check (id (id (A:=TYPE))).

Definition TYPE1 := TYPE.
Print TYPE. Print TYPE1.
Check I'' TYPE.
Check I'' TYPE.


Print I''. Print I.
