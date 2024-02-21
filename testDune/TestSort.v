Set Universe Polymorphism.
Set Primitive Projections.

Record Sum@{q |a b|} (A : Type@{q|a}) (B : A -> Type@{q|b}) : Type@{q | max(a,b)} :=
  pair { fst : A ; snd : B fst }.

Inductive Id@{q|a|} {A : Type@{q|a}} (x : A) : A -> Type@{q|a} := refl : Id x x.
Notation "x ≡ y" := (Id x y) (at level 65).

Record catop := { 
  obj :> Set ; 
  hom :> obj -> obj -> Set ; 
  comp : forall {x y z : obj} (f : hom x y) (g : hom y z), hom x z ;
  id : forall x, hom x x
}.

From Coq Require Import PeanoNat.
Definition natCat : catop :=  
  {| obj := nat ; hom n m := n <= m ; comp := Nat.le_trans ; id := Nat.le_refl |}.

Definition cast {A B : Set} (e : A = B) : A -> B :=
  match e with eq_refl => fun x => x end.

Sort psh.

Definition Psh@{u} := Type@{psh|u}.
Definition Psh'@{u} := Type@{psh|u+1}.
Symbol psh@{u} : Psh'@{u}. (* Psh@{u+1} *)
Symbol yon : natCat.(obj) -> Psh@{Set}.

Symbol on@{u} : Psh@{u} -> natCat.(obj) -> Type@{u}.
Symbol act@{u} : forall (X : Psh@{u}) {n m}, hom natCat n m -> on X m -> on X n.

Record natTrans@{u} (X Y : Psh@{u}) :=
  { map :> forall n, on X n -> on Y n ;
    natural : forall {n m} (f : hom natCat n m) (xm : on X m),
      act Y f (map m xm) ≡ map n (act X f xm)
  }.

Record dPsh@{u} {X : Psh@{u}} := mkDPsh { total :> Psh@{u} ; display : natTrans total X }.
Arguments dPsh : clear implicits.

(* Definition ond@{u} {X : Psh@{u}} (Y : dPsh X) (n : natCat) (x : on X n) :=
  { y : on Y n & display Y n y = x }. *)

(* Definition X@{u} n := dPsh@{u+1} (yon n). Type@{u+2}. *)

Rewrite Rule on_psh := @{u v | u < v } |- on@{v} psh@{u} ?n ==> (dPsh@{u} (yon ?n) : Type@{v}).
Rewrite Rule on_yon := on (yon ?n) ?m ==> hom natCat ?m ?n.
Rewrite Rule act_yon := @act (yon ?n) ?k ?l ?f ?h ==> @comp natCat ?k ?l ?n ?f ?h.

Module Type CatSIG.
  Sort q.
  Monomorphic Universe u.
  Definition Tq@{v} := Type@{q|v}.
  Axiom Obj : Type@{q|u}.
  Axiom Hom : Obj -> Obj -> Type@{q|u}.
  Axiom id : forall (A : Obj), Hom A A.
  Axiom comp : forall (A B C : Obj), Hom A B -> Hom B C -> Hom A C.
End CatSIG.

Module Presheaf(C : CatSIG).
  Sort p.
  Definition Ps@{u} := Type@{p|u}.
  Set Printing Universes.
  Symbol on@{u} : Ps@{u} -> C.Obj -> C.Tq@{u}.


Definition pb (X1 X2 : Psh@{u}) (α : natTrans X1 X2) (Y : dPsh X2) : dPsh X1 :=
  Sum X1 (fun x1 => Sum Y (fun y => ))

Record psh@{s|u v|} {C : catop} := {
    Idx := Type@{s|u} ;

    on : Idx -> C -> Set ;
    act : forall (X : Idx) {x y : C} (f : hom C x y), on X y -> on X x ;
    act_id : forall (X : Idx) (x : C) (a : on X x), act X (id C x) a = a ;
    act_comp : forall (X : Idx) {x y z: C} (f : hom C x y) (g : hom C y z) (a : on X z), 
      act X (comp C f g) a = act X f (act X g a) ;

    discr : Set ->  Idx ;
    on_discr : forall A x, A = on (discr A) x;
    act_discr : forall (A : Set) {x y} (f : hom C x y) (a : A),
      act (discr A) f (cast (on_discr A y) a) = cast (on_discr A x) a ;

    yon : C -> Idx ;
    on_yon : forall x y, hom C x y = on (yon y) x ;
    act_yon : forall {x y z} (f : hom C x y) (g : hom C y z),
      act (yon z) f (cast (on_yon y z) g) = cast (on_yon x z) (comp C f g) ;
}.

Arguments psh : clear implicits.

Set Allow Rewrite Rules.


Symbol Trees : psh natCat.

Inductive terminal : Trees.(Idx) := uniq : terminal.

Set Printing Universes.
Check Trees.(Idx).

Definition id'@{u} (A : Type@{u}) : A -> A := fun x => x.

Check id' Trees.(Idx).

Rewrite Rule on_discr_rw := Trees.(on) (Trees.(discr) ?A) ?x ==> ?A.
Rewrite Rule act_discr_rw := Trees.(act) (Trees.(discr) ?A) ?f ?x ==> ?x.

Record nat_trans (A : Trees.(Idx)) (B : A -> Tree.(Idx)) (n : natCat) :=
  {| 
    map :> forall {p} (α : hom natCat p n) (a : Trees.(on) A p), Trees.(on) (B a) p ;
    natural : forall {p q} (α : hom natCat p n) (β : hom natCat q p),
      Trees.(act) (B a) β (map α a) = map (comp natCat β α) a
  |}

Rewrite Rule on_forall_rw  := Trees.(on) (forall x : ?A, ?B) ?x ==> ()





Set Definitional UIP.
Inductive Eq {A} (x : A) : A -> SProp := refl : Eq x x.
Inductive Box@{u} (P : SProp) : Type@{u} := box : P -> Box P.
