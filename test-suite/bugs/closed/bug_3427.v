Require Import TestSuite.admit.
(* -*- mode: coq; coq-prog-args: ("-indices-matter") -*- *)
(* File reduced by coq-bug-finder from original input, then from 0 lines to 7171 lines, then from 7184 lines to 558 lines, then from 556 lines to 209 lines *)
Generalizable All Variables.
Set Universe Polymorphism.
Notation Type0 := Set.
Notation idmap := (fun x => x).
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) := fun x => g (f x).
Notation "g 'o' f" := (compose g f) (at level 40, left associativity) : function_scope.
Open Scope function_scope.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Arguments idpath {A a} , [A] a.
Delimit Scope path_scope with path.
Local Open Scope path_scope.
Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z := match p, q with idpath, idpath => idpath end.
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x := match p with idpath => idpath end.
Notation "1" := idpath : path_scope.
Notation "p @ q" := (concat p q) (at level 20) : path_scope.
Notation "p ^" := (inverse p) (at level 3) : path_scope.
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y := match p with idpath => u end.
Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y := match p with idpath => idpath end.
Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x) := forall x:A, f x = g x.
Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.
Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g) : forall x, f x = g x := fun x => match h with idpath => idpath end.
Definition Sect {A B : Type} (s : A -> B) (r : B -> A) := forall x : A, r (s x) = x.
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
                                               equiv_inv : B -> A ;
                                               eisretr : Sect equiv_inv f;
                                               eissect : Sect f equiv_inv;
                                               eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
                                             }.
Record Equiv A B := BuildEquiv {
                        equiv_fun :> A -> B ;
                        equiv_isequiv :> IsEquiv equiv_fun
                      }.

Delimit Scope equiv_scope with equiv.

Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3) : equiv_scope.

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

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.

Notation Contr := (IsTrunc minus_two).
Notation IsHProp := (IsTrunc minus_one).
Notation IsHSet := (IsTrunc 0).

Class Funext :=
  { isequiv_apD10 :> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }.

Definition concat_pV {A : Type} {x y : A} (p : x = y) :
  p @ p^ = 1
  :=
    match p with idpath => 1 end.

Definition concat_Vp {A : Type} {x y : A} (p : x = y) :
  p^ @ p = 1
  :=
    match p with idpath => 1 end.

Definition transport_pp {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  p @ q # u = q # p # u :=
  match q with idpath =>
               match p with idpath => 1 end
  end.

Definition transport2 {A : Type} (P : A -> Type) {x y : A} {p q : x = y}
           (r : p = q) (z : P x)
: p # z = q # z
  := ap (fun p' => p' # z) r.

Inductive Unit : Type0 :=
  tt : Unit.

Instance contr_unit : Contr Unit | 0 := let x := {|
                                              center := tt;
                                              contr := fun t : Unit => match t with tt => 1 end
                                            |} in x.

Instance trunc_succ `{IsTrunc n A} : IsTrunc (trunc_S n) A | 1000.
admit.
Defined.

Record hProp := hp { hproptype :> Type ; isp : IsHProp hproptype}.
Definition Unit_hp:hProp:=(hp Unit _).

Global Instance isequiv_ap_hproptype `{Funext} X Y : IsEquiv (@ap _ _ hproptype X Y).
admit.
Defined.

Definition path_hprop `{Funext} X Y := (@ap _ _ hproptype X Y)^-1%equiv.

Record hSet := BuildhSet {setT:> Type; iss :> IsHSet setT}.
Local Open Scope equiv_scope.

Instance isequiv_path {A B : Type} (p : A = B)
: IsEquiv (transport (fun X:Type => X) p) | 0
  := BuildIsEquiv _ _ _ (transport (fun X:Type => X) p^)
                  (fun b => ((transport_pp idmap p^ p b)^ @ transport2 idmap (concat_Vp p) b))
                  (fun a => ((transport_pp idmap p p^ a)^ @ transport2 idmap (concat_pV p) a))
                  (fun a => match p in _ = C return
                                  (transport_pp idmap p^ p (transport idmap p a))^ @
                                                                                     transport2 idmap (concat_Vp p) (transport idmap p a) =
                                  ap (transport idmap p) ((transport_pp idmap p p^ a) ^ @
                                                                                          transport2 idmap (concat_pV p) a) with idpath => 1 end).

Definition equiv_path (A B : Type) (p : A = B) : A <~> B
  := BuildEquiv _ _ (transport (fun X:Type => X) p) _.

Class Univalence := {
                     isequiv_equiv_path :> forall (A B : Type), IsEquiv (equiv_path A B)
                   }.

Section Univalence.
  Context `{Univalence}.

  Definition path_universe_uncurried {A B : Type} (f : A <~> B) : A = B
    := (equiv_path A B)^-1 f.
End Univalence.

Local Inductive minus1Trunc (A :Type) : Type :=
  min1 : A -> minus1Trunc A.

Instance minus1Trunc_is_prop {A : Type} : IsHProp (minus1Trunc A) | 0.
admit.
Defined.

Definition hexists {X} (P:X->Type):Type:= minus1Trunc (sigT  P).

Section AssumingUA.

  Definition isepi {X Y} `(f:X->Y) := forall Z: hSet,
                                      forall g h: Y -> Z, g o f = h o f -> g = h.
  Context {X Y : hSet} (f : X -> Y) (Hisepi : isepi f).

  Goal forall (X Y : hSet) (f : forall _ : setT X, setT Y),
         let fib :=
             fun y : setT Y =>
               hp (@hexists (setT X) (fun x : setT X => @paths (setT Y) (f x) y))
                  (@minus1Trunc_is_prop
                     (@sigT (setT X) (fun x : setT X => @paths (setT Y) (f x) y))) in
         forall (x : setT X) (_ : Univalence) (_ : Funext),
           @paths hProp (fib (f x)) Unit_hp.
  intros.

  apply path_hprop.
  simpl.
  Set Printing Universes.
  Set Printing All.
  refine (path_universe_uncurried _).
  Undo.
  apply path_universe_uncurried. (* Toplevel input, characters 21-44:
Error: Refiner was given an argument
 "@path_universe_uncurried (* Top.425 Top.426 Top.427 Top.428 Top.429 *) X1
    (@hexists (* Top.405 Top.404 Set Set *) (setT (* Top.405 *) X0)
       (fun x0 : setT (* Top.405 *) X0 =>
        @paths (* Top.404 *) (setT (* Top.404 *) Y0) (f0 x0) (f0 x))) Unit
    ?63" of type
 "@paths (* Top.428 *) Type (* Top.425 *)
    (@hexists (* Top.405 Top.404 Set Set *) (setT (* Top.405 *) X0)
       (fun x0 : setT (* Top.405 *) X0 =>
        @paths (* Top.404 *) (setT (* Top.404 *) Y0) (f0 x0) (f0 x))) Unit"
instead of
 "@paths (* Top.413 *) Type (* Set *)
    (@hexists (* Top.405 Top.404 Set Set *) (setT (* Top.405 *) X0)
       (fun x0 : setT (* Top.405 *) X0 =>
        @paths (* Top.404 *) (setT (* Top.404 *) Y0) (f0 x0) (f0 x))) Unit".
 *)
