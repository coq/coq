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
  comp {o o' o''} : hom o' o'' -> hom o o' -> hom o o'' ;
  comp_id_l o o' (f : hom o' o) : comp (id_obj o) f = f ;
  comp_id_r o o' (f : hom o o') : comp f (id_obj o) = f }.
Class Functor {A H B H'} (C : Category A H) (D : Category B H') := {
  fmap : A -> B;
  fmap_F {a b} : H a b -> H' (fmap a) (fmap b) ;
  fmap_id a : fmap_F (id_obj a) = id_obj (fmap a)

}.


Instance TYPE_cat : Category TYPE (fun a b => a -> b) := 
  { id_obj o := id; comp o o' o'' g f := fun x => g (f x) }.

Instance ID_Functor {A H} (C : Category A H) : Functor C C := {
  fmap a := a ;
  fmap_F a b f := f }.
Proof. reflexivity. Qed.

Record category := {
  obj : Type ; hom : crelation obj; cat : Category obj hom }.

Record functor (c d : category) := mkFunctor {
  funct : Functor (cat c) (cat d) }.

Instance functor_cat : Category category functor. admit. Qed.

(* := { *)
(*   id_obj o := mkFunctor _ _ (ID_Functor (cat o)); *)
(*   comp o o' o'' := _ *)
(* }. *)
(* Proof. admit. intros.  constructor.  apply (ID_Functor (cat o)).  admit. *)

(* Qed. *)

Class nat_trans {A H B H'} (C : Category A H) (D : Category B H') (F G : Functor C D) := {
  nat_transform o : H' (fmap (Functor:=F) o) (fmap (Functor:=G) o) ;
  nat_natural X Y (f : H X Y) : comp (nat_transform Y) (fmap_F (Functor:=F) f) =
  comp (fmap_F (Functor:=G) f) (nat_transform X)
}.

Record nat_transf {C D} (F G : functor C D) := mkNatTransf {
  nat_transfo : nat_trans (cat C) (cat D) (funct _ _ F) (funct _ _ G) }.

Instance id_nat_trans {A H B H'} (C : Category A H) (D : Category B H') (F : Functor C D) : 
  nat_trans _ _ F F :=
  { nat_transform o := fmap_F (id_obj o) }.
Proof. intros. rewrite !fmap_id, comp_id_l, comp_id_r. reflexivity. Qed.

Instance nat_trans_cat C D : Category (functor C D) (@nat_transf C D) := 
  { id_obj o := {| nat_transfo := id_nat_trans _ _ (funct _ _ o) |} }.
Proof. simpl.


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
