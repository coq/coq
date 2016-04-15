Unset Strict Universe Declaration.
Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 9113 lines to 279 lines *)
(* coqc version trunk (October 2014) compiled on Oct 19 2014 18:56:9 with OCaml 3.12.1
   coqtop version trunk (October 2014) *)

Notation Type0 := Set.

Notation idmap := (fun x => x).

Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Open Scope fibration_scope.

Notation pr1 := projT1.

Notation "x .1" := (pr1 x) (at level 3, format "x '.1'") : fibration_scope.

Definition compose {A B C : Type} (g : B -> C) (f : A -> B) :=
  fun x => g (f x).

Notation "g 'o' f" := (compose g f) (at level 40, left associativity) : function_scope.
Open Scope function_scope.

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x.
admit.
Defined.

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.

Notation "1" := idpath : path_scope.

Notation "p @ q" := (concat p q) (at level 20) : path_scope.

Notation "p ^" := (inverse p) (at level 3, format "p '^'") : path_scope.

Notation "p @' q" := (concat p q) (at level 21, left associativity,
  format "'[v' p '/' '@''  q ']'") : long_path_scope.
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y.
exact (match p with idpath => u end).
Defined.

Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y.
exact (match p with idpath => idpath end).
Defined.

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, f x = g x.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Arguments eisretr {A B} f {_} _.

Record Equiv A B := BuildEquiv {
  equiv_fun : A -> B ;
  equiv_isequiv : IsEquiv equiv_fun
}.

Coercion equiv_fun : Equiv >-> Funclass.

Global Existing Instance equiv_isequiv.

Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'") : equiv_scope.

Class Contr_internal (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Notation "n .+1" := (trunc_S n) (at level 2, left associativity, format "n .+1") : trunc_scope.
Local Open Scope trunc_scope.
Notation "-2" := minus_two (at level 0) : trunc_scope.
Notation "-1" := (-2.+1) (at level 0) : trunc_scope.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | -2 => Contr_internal A
    | n'.+1 => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.
Notation IsHProp := (IsTrunc -1).

Monomorphic Axiom dummy_funext_type : Type0.
Monomorphic Class Funext := { dummy_funext_value : dummy_funext_type }.

Local Open Scope path_scope.

Definition concat_p1 {A : Type} {x y : A} (p : x = y) :
  p @ 1 = p
  :=
  match p with idpath => 1 end.

Definition concat_1p {A : Type} {x y : A} (p : x = y) :
  1 @ p = p
  :=
  match p with idpath => 1 end.

Definition concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @ (q @ r) = (p @ q) @ r :=
  match r with idpath =>
    match q with idpath =>
      match p with idpath => 1
      end end end.

Definition concat_pp_p {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  (p @ q) @ r = p @ (q @ r) :=
  match r with idpath =>
    match q with idpath =>
      match p with idpath => 1
      end end end.

Definition moveL_Mp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  r^ @ q = p -> q = r @ p.
admit.
Defined.

Ltac with_rassoc tac :=
  repeat rewrite concat_pp_p;
  tac;

  repeat rewrite concat_p_pp.

Ltac rewrite_moveL_Mp_p := with_rassoc ltac:(apply moveL_Mp).

Definition ap_p_pp {A B : Type} (f : A -> B) {w : B} {x y z : A}
  (r : w = f x) (p : x = y) (q : y = z) :
  r @ (ap f (p @ q)) = (r @ ap f p) @ (ap f q).
admit.
Defined.

Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (g o f) p = ap g (ap f p)
  :=
  match p with idpath => 1 end.

Definition concat_Ap {A B : Type} {f g : A -> B} (p : forall x, f x = g x) {x y : A} (q : x = y) :
  (ap f q) @ (p y) = (p x) @ (ap g q)
  :=
  match q with
    | idpath => concat_1p _ @ ((concat_p1 _) ^)
  end.

Definition transportD2 {A : Type} (B C : A -> Type) (D : forall a:A, B a -> C a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1) (w : D x1 y z)
  : D x2 (p # y) (p # z)
  :=
  match p with idpath => w end.
Local Open Scope equiv_scope.

Definition transport_arrow_toconst {A : Type} {B : A -> Type} {C : Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 -> C) (y : B x2)
  : (transport (fun x => B x -> C) p f) y  =  f (p^ # y).
admit.
Defined.

Definition transport_arrow_fromconst {A B : Type} {C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B -> C x1) (y : B)
  : (transport (fun x => B -> C x) p f) y  =  p # (f y).
admit.
Defined.

Definition ap_transport_arrow_toconst {A : Type} {B : A -> Type} {C : Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 -> C) {y1 y2 : B x2} (q : y1 = y2)
  : ap (transport (fun x => B x -> C) p f) q
    @ transport_arrow_toconst p f y2
    = transport_arrow_toconst p f y1
    @ ap (fun y => f (p^ # y)) q.
admit.
Defined.

Class Univalence.
Definition path_universe {A B : Type} (f : A -> B) {feq : IsEquiv f} : (A = B).
admit.
Defined.
Definition transport_path_universe
           {A B : Type} (f : A -> B) {feq : IsEquiv f} (z : A)
  : transport (fun X:Type => X) (path_universe f) z = f z.
admit.
Defined.
Definition transport_path_universe_V `{Funext}
           {A B : Type} (f : A -> B) {feq : IsEquiv f} (z : B)
  : transport (fun X:Type => X) (path_universe f)^ z = f^-1 z.
admit.
Defined.

Ltac simpl_do_clear tac term :=
  let H := fresh in
  assert (H := term);
    simpl in H |- *;
    tac H;
    clear H.

Tactic Notation "simpl" "rewrite"      constr(term) := simpl_do_clear ltac:(fun H => rewrite    H) term.

Global Instance Univalence_implies_Funext `{Univalence} : Funext.
Admitted.

Section Factorization.

  Context {class1 class2 : forall (X Y : Type@{i}), (X -> Y) -> Type@{i}}
          `{forall (X Y : Type@{i}) (g:X->Y), IsHProp (class1 _ _ g)}
          `{forall (X Y : Type@{i}) (g:X->Y), IsHProp (class2 _ _ g)}
          {A B : Type@{i}} {f : A -> B}.

  Record Factorization :=
    { intermediate : Type ;
      factor1 : A -> intermediate ;
      factor2 : intermediate -> B ;
      fact_factors : factor2 o factor1 == f ;
      inclass1 : class1 _ _ factor1 ;
      inclass2 : class2 _ _ factor2
    }.

  Record PathFactorization {fact fact' : Factorization} :=
    { path_intermediate : intermediate fact <~> intermediate fact' ;
      path_factor1 : path_intermediate o factor1 fact == factor1 fact' ;
      path_factor2 : factor2 fact == factor2 fact' o path_intermediate ;
      path_fact_factors : forall a, path_factor2 (factor1 fact a)
                          @ ap (factor2 fact') (path_factor1 a)
                          @ fact_factors fact' a
                          = fact_factors fact a
    }.
    Context `{Univalence} {fact fact' : Factorization}
            (pf : @PathFactorization fact fact').

    Let II := path_intermediate pf.
    Let ff1 := path_factor1 pf.
    Let ff2 := path_factor2 pf.
Local Definition II' : intermediate fact = intermediate fact'.
admit.
Defined.

    Local Definition fff' (a : A)
    : (transportD2 (fun X => A -> X) (fun X => X -> B)
                   (fun X g h => {_ : forall a : A, h (g a) = f a &
                                  {_ : class1 A X g & class2 X B h}})
                   II' (factor1 fact) (factor2 fact)
                   (fact_factors fact; (inclass1 fact; inclass2 fact))).1 a =
      ap (transport (fun X => X -> B) II' (factor2 fact))
        (transport_arrow_fromconst II' (factor1 fact) a
          @ transport_path_universe II (factor1 fact a)
          @ ff1 a)
        @ transport_arrow_toconst II' (factor2 fact) (factor1 fact' a)
        @ ap (factor2 fact) (transport_path_universe_V II (factor1 fact' a))
        @ ff2 (II^-1 (factor1 fact' a))
        @ ap (factor2 fact') (eisretr II (factor1 fact' a))
        @ fact_factors fact' a.
    Proof.

      Open Scope long_path_scope.

      rewrite (ap_transport_arrow_toconst (B := idmap) (C := B)).

      simpl rewrite (@ap_compose _ _ _ (transport idmap (path_universe II)^)
                                 (factor2 fact)).
      rewrite <- ap_p_pp; rewrite_moveL_Mp_p.
      Set Debug Tactic Unification.
      Fail rewrite (concat_Ap ff2).
