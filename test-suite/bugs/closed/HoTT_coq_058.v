Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from 10044 lines to 493 lines, then from 425 lines to 160 lines. *)
Set Universe Polymorphism.
Notation idmap := (fun x => x).
Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Open Scope fibration_scope.
Notation "x .1" := (projT1 x) (at level 3) : fibration_scope.
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.
Arguments idpath {A a} , [A] a.
Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Delimit Scope path_scope with path.
Local Open Scope path_scope.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
: forall x, f x = g x
  := fun x => match h with idpath => idpath end.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv { equiv_inv : B -> A }.

Delimit Scope equiv_scope with equiv.
Local Open Scope equiv_scope.

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3) : equiv_scope.

Class Funext := { isequiv_apD10 :> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }.

Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) :
  (forall x, f x = g x) -> f = g
  := (@apD10 A P f g)^-1.

Inductive Unit : Set :=
  tt : Unit.

Definition path_prod_uncurried {A B : Type} (z z' : A * B)
           (pq : (fst z = fst z') * (snd z = snd z'))
: (z = z')
  := match pq with (p,q) =>
                   match z, z' return
                         (fst z = fst z') -> (snd z = snd z') -> (z = z') with
                     | (a,b), (a',b') => fun p q =>
                                           match p, q with
                                               idpath, idpath => idpath
                                           end
                   end p q
     end.

Definition path_prod {A B : Type} (z z' : A * B) :
  (fst z = fst z') -> (snd z = snd z') -> (z = z')
  := fun p q => path_prod_uncurried z z' (p,q).

Definition path_prod' {A B : Type} {x x' : A} {y y' : B}
: (x = x') -> (y = y') -> ((x,y) = (x',y'))
  := fun p q => path_prod (x,y) (x',y') p q.

Lemma path_forall_recr_beta `{Funext} A B x0 P f g e Px
: @transport (forall a : A, B a)
             (fun f => P f (f x0))
             f
             g
             (@path_forall _ _ _ _ _ e)
             Px
  = @transport ((forall a, B a) * B x0)%type
               (fun x => P (fst x) (snd x))
               (f, f x0)
               (g, g x0)
               (path_prod' (@path_forall _ _ _ _ _ e) (e x0))
               Px.

  admit.
Defined.
Definition transport_path_prod'_beta' A B P (x x' : A) (y y' : B) (HA : x = x') (HB : y = y') (Px : P x y)
: @transport (A * B) (fun xy => P (fst xy) (snd xy)) (x, y) (x', y') (@path_prod' A B x x' y y' HA HB) Px
  = @transport A (fun x => P x y') x x' HA
               (@transport B (fun y => P x y) y y' HB Px).
  admit.
Defined.
Goal forall (T : Type) (T0 : T -> T -> Type)
            (Pmor : forall s d : T, T0 s d -> Type) (x x0 : T)
            (x1 : T0 x x0) (p : Pmor x x0 x1) (H : Funext),
       transport
         (fun x2 : {_ : T & Unit} -> {_ : T & Unit} =>
            { x1 : _ & Pmor (x2 (x; tt)) .1 (x2 (x0; tt)) .1 x1})
         (path_forall (fun c : {_ : T & Unit} => (c .1; tt)) idmap
                      (fun x2 : {_ : T & Unit} =>
                         let (x3, y) as s return ((s .1; tt) = s) := x2 in
                         match y as y0 return ((x3; tt) = (x3; y0)) with
                           | tt => idpath
                         end)) (x1; p) = (x1; p).
intros.
let F := match goal with |- context[@transport _ (fun x0 => @?F x0) _ _ (@path_forall ?H ?X ?T ?f ?g ?e)] => constr:(F) end in
let H := match goal with |- context[@transport _ (fun x0 => @?F x0) _ _ (@path_forall ?H ?X ?T ?f ?g ?e)] => constr:(H) end in
let X := match goal with |- context[@transport _ (fun x0 => @?F x0) _ _ (@path_forall ?H ?X ?T ?f ?g ?e)] => constr:(X) end in
let T := match goal with |- context[@transport _ (fun x0 => @?F x0) _ _ (@path_forall ?H ?X ?T ?f ?g ?e)] => constr:(T) end in
let t0 := fresh "t0" in
let t1 := fresh "t1" in
let T1 := lazymatch type of F with (?T -> _) -> _ => constr:(T) end in
    evar (t1 : T1);
  let T0 := lazymatch type of F with (forall a : ?A, @?B a) -> ?C => constr:((forall a : A, B a) -> B t1 -> C) end in
      evar (t0 : T0);

    let dummy := fresh in
    assert (dummy : forall x0, F x0 = t0 x0 (x0 t1));
      [ let x0 := fresh in
        intro x0;
          simpl in *;
          let GL0 := lazymatch goal with |- ?GL0 = _ => constr:(GL0) end in
              let GL0' := fresh in
              let GL1' := fresh in
              set (GL0' := GL0);

                let arg := match GL0 with context[x0 ?arg] => constr:(arg) end in
                assert (t1 = arg) by (subst t1; reflexivity); subst t1;
                pattern (x0 arg) in GL0';
                match goal with
                  | [ GL0'' := ?GR _ |- _ ] => constr_eq GL0' GL0'';
                                              pose GR as GL1'
                end;

                pattern x0 in GL1';
                match goal with
                  | [ GL1'' := ?GR _ |- _ ] => constr_eq GL1' GL1'';
                                              assert (t0 = GR)
                end;
                subst t0; [ reflexivity | reflexivity ]
            | clear dummy ];
      let p := fresh in
      pose (@path_forall_recr_beta H X T t1 t0) as p;
        simpl in *;
        rewrite p;
        subst t0 t1 p.
      rewrite transport_path_prod'_beta'.
      (* Anomaly: Uncaught exception Invalid_argument("to_constraints: non-trivial algebraic constraint between universes", _).
Please report. *)
