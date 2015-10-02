Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 8249 lines to 907 lines, then from 843 lines to 357 lines, then from 351 lines to 260 lines, then from 208 lines to 162 lines, then from 167 lines to 154 lines *)
Set Universe Polymorphism.
Generalizable All Variables.
Reserved Notation "g 'o' f" (at level 40, left associativity).
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.
Arguments idpath {A a} , [A] a.
Notation "x = y" := (@paths _ x y) : type_scope.

Class IsEquiv {A B : Type} (f : A -> B) := {}.

Class Contr_internal (A : Type) := BuildContr {
                                       center : A ;
                                       contr : (forall y : A, center = y)
                                     }.

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Fixpoint nat_to_trunc_index (n : nat) : trunc_index
  := match n with
       | 0 => trunc_S (trunc_S minus_two)
       | S n' => trunc_S (nat_to_trunc_index n')
     end.

Coercion nat_to_trunc_index : nat >-> trunc_index.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | minus_two => Contr_internal A
    | trunc_S n' => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Notation minus_one:=(trunc_S minus_two).

Class IsTrunc (n : trunc_index) (A : Type) : Type := Trunc_is_trunc : IsTrunc_internal n A.

Notation Contr := (IsTrunc minus_two).
Notation IsHProp := (IsTrunc minus_one).
Notation IsHSet := (IsTrunc 0).

Class Funext := {}.
Inductive Unit : Set := tt.

Instance contr_unit : Contr Unit | 0 := let x := {|
                                              center := tt;
                                              contr := fun t : Unit => match t with tt => idpath end
                                            |} in x.
Instance trunc_succ `{IsTrunc n A} : IsTrunc (trunc_S n) A | 1000.
admit.
Defined.
Record hProp := hp { hproptype :> Type ; isp : IsHProp hproptype}.
Definition Unit_hp:hProp:=(hp Unit _).
Record hSet := BuildhSet {setT:> Type; iss :> IsHSet setT}.
Canonical Structure default_HSet:= fun T P => (@BuildhSet T P).
Definition ismono {X Y} (f : X -> Y)
  := forall Z : hSet,
     forall g h : Z -> X, (fun x => f (g x)) = (fun x => f (h x)) -> g = h.

Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope object_scope with object.
Record PreCategory :=
  Build_PreCategory {
      object :> Type;
      morphism : object -> object -> Type;
      compose : forall s d d', morphism d d' -> morphism s d -> morphism s d'
    }.
Arguments compose [!C s d d'] m1 m2 : rename.

Infix "o" := compose : morphism_scope.
Local Open Scope morphism_scope.

Class IsEpimorphism {C} {x y} (m : morphism C x y) :=
  is_epimorphism : forall z (m1 m2 : morphism C y z),
                     m1 o m = m2 o m
                     -> m1 = m2.

Class IsMonomorphism {C} {x y} (m : morphism C x y) :=
  is_monomorphism : forall z (m1 m2 : morphism C z x),
                      m o m1 = m o m2
                      -> m1 = m2.
Class Univalence := {}.
Global Instance isset_hProp `{Funext} : IsHSet hProp | 0. Admitted.

Definition set_cat : PreCategory
  := @Build_PreCategory hSet
                        (fun x y => forall _ : x, y)%core
                        (fun _ _ _ f g x => f (g x))%core.
Local Inductive minus1Trunc (A :Type) : Type := min1 : A -> minus1Trunc A.
Instance minus1Trunc_is_prop {A : Type} : IsHProp (minus1Trunc A) | 0. Admitted.
Definition hexists {X} (P:X->Type):Type:= minus1Trunc (sigT  P).
Definition isepi {X Y} `(f:X->Y) := forall Z: hSet,
                                    forall g h: Y -> Z, (fun x => g (f x)) = (fun x => h (f x)) -> g = h.
Definition issurj {X Y} (f:X->Y) := forall y:Y , hexists (fun x => (f x) = y).
Lemma isepi_issurj `{fs:Funext} `{ua:Univalence} `{fs' : Funext} {X Y} (f:X->Y): isepi f -> issurj f.
Proof.
  intros epif y.
  set (g :=fun _:Y => Unit_hp).
  set (h:=(fun y:Y => (hp (hexists (fun _ : Unit => {x:X & y = (f x)})) _ ))).
  clear fs'.
  hnf in epif.
  specialize (epif (BuildhSet hProp _) g h).
  admit.
Defined.
Definition isequiv_isepi_ismono `{Univalence, fs0 : Funext} (X Y : hSet) (f : X -> Y) (epif : isepi f) (monof : ismono f)
: IsEquiv f.
Proof.
  pose proof (@isepi_issurj _ _ _ _ _ f epif) as surjf.
  admit.
Defined.
Section fully_faithful_helpers.
  Context `{fs0 : Funext}.
  Variables x y : hSet.
  Variable m : x -> y.

  Fail Let isequiv_isepi_ismono_helper ua :=
    (@isequiv_isepi_ismono ua fs0 x y m : isepi m -> ismono m -> IsEquiv m).

  Goal True.
  Fail set (isequiv_isepimorphism_ismonomorphism
       := fun `{Univalence}
              (Hepi : IsEpimorphism (m : morphism set_cat x y))
              (Hmono : IsMonomorphism (m : morphism set_cat x y))
          => (@isequiv_isepi_ismono_helper _ Hepi Hmono : @IsEquiv _ _ m)).
  admit.
  Undo.
  Fail set (isequiv_isepimorphism_ismonomorphism
       := fun `{Univalence}
              (Hepi : IsEpimorphism (m : morphism set_cat x y))
              (Hmono : IsMonomorphism (m : morphism set_cat x y))
          => ((let _ := @isequiv_isepimorphism_ismonomorphism _ Hepi Hmono in @isequiv_isepi_ismono _ fs0 x y m Hepi Hmono)
              : @IsEquiv _ _ m)).
  Set Printing Universes.
  admit. (* Error: Universe inconsistency (cannot enforce Top.235 <= Set because Set
< Top.235). *)
