(* -*- mode: coq; coq-prog-args: ("-noinit" "-indices-matter") -*- *)

Declare ML Module "ltac_plugin".
Global Set Default Proof Mode "Classic".

Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).

Reserved Notation "x = y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x = y" (at level 70, no associativity).
Reserved Notation "p # x" (right associativity, at level 65).
Reserved Notation "f == g" (at level 70, no associativity).

Reserved Notation "A <~> B" (at level 85).
Reserved Notation "f ^-1" (at level 3, format "f '^-1'").

Reserved Infix "$->" (at level 99).
Reserved Infix "$<~>" (at level 85).
Reserved Infix "$o" (at level 40, left associativity).
Reserved Infix "$==" (at level 70).
Reserved Notation "g 'o' f" (at level 40, left associativity).
Declare Scope type_scope.
Declare Scope path_scope.
Delimit Scope function_scope with function.
Global Open Scope path_scope.
Global Open Scope function_scope.
Global Open Scope type_scope.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

Global Set Primitive Projections.

Global Set Printing Primitive Projection Parameters.

Definition Relation (A : Type) := A -> A -> Type.

Class Reflexive {A} (R : Relation A) :=
  reflexivity : forall x : A, R x x.

Ltac old_reflexivity := reflexivity.
Tactic Notation "reflexivity" :=
  old_reflexivity
|| (intros;
  let R := match goal with |- ?R ?x ?y => constr:(R) end in
  let pre_proof_term_head := constr:(@reflexivity _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  apply (proof_term_head : forall x, R x x)).

Notation Type0 := Set.

Notation idmap := (fun x => x).

Notation compose := (fun g f x => g (f x)).

Notation "g 'o' f" := (compose g%function f%function) : function_scope.

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Notation "1" := idpath : path_scope.
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y.
exact (match p with idpath => u end).
Defined.

Notation "p # x" := (transport _ p x) (only parsing) : path_scope.
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y.
Admitted.

Definition pointwise_paths A (P : A -> Type) (f g : forall x, P x)
  := forall x, f x = g x.

Global Arguments pointwise_paths {A}%type_scope {P} (f g)%function_scope.

Notation "f == g" := (pointwise_paths f g) : type_scope.

Class IsEquiv {A B : Type} (f : A -> B) := {
  equiv_inv : B -> A ;
  eisretr : f o equiv_inv == idmap ;
  eissect : equiv_inv o f == idmap ;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x) ;
}.

Arguments eisretr {A B}%type_scope f%function_scope {_} _.

Record Equiv A B := {
  equiv_fun : A -> B ;
  equiv_isequiv : IsEquiv equiv_fun
}.

Coercion equiv_fun : Equiv >-> Funclass.

Global Existing Instance equiv_isequiv.

Notation "A <~> B" := (Equiv A B) : type_scope.

Notation "f ^-1" := (@equiv_inv _ _ f _) : function_scope.

Tactic Notation "do_with_holes" tactic3(x) uconstr(p) :=
  x uconstr:(p) ||
  x uconstr:(p _) ||
  x uconstr:(p _ _) ||
  x uconstr:(p _ _ _) ||
  x uconstr:(p _ _ _ _) ||
  x uconstr:(p _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Class IsGlobalAxiom (A : Type) : Type0 := {}.

Ltac is_global_axiom A := let _ := constr:(_ : IsGlobalAxiom A) in idtac.

Ltac global_axiom := try match goal with
    | |- ?G  => is_global_axiom G; exact _
end.

Tactic Notation "srefine" uconstr(term) := simple refine term.

Tactic Notation "nrefine" uconstr(term) := notypeclasses refine term; global_axiom.

Tactic Notation "snrefine" uconstr(term) := simple notypeclasses refine term; global_axiom.

Tactic Notation "rapply" uconstr(term)
  := do_with_holes ltac:(fun x => refine x) term.

Tactic Notation "srapply" uconstr(term)
  := do_with_holes ltac:(fun x => srefine x) term.

Tactic Notation "nrapply" uconstr(term)
  := do_with_holes ltac:(fun x => nrefine x) term.

Tactic Notation "snrapply" uconstr(term)
  := do_with_holes ltac:(fun x => snrefine x) term.
Definition transport_1 {A : Type} (P : A -> Type) {x : A} (u : P x)
  : 1 # u = u.
Admitted.

Class IsGraph (A : Type) :=
{
  Hom : A -> A -> Type
}.

Notation "a $-> b" := (Hom a b).

Class Is01Cat (A : Type) `{IsGraph A} :=
{
  Id  : forall (a : A), a $-> a;
  cat_comp : forall (a b c : A), (b $-> c) -> (a $-> b) -> (a $-> c);
}.

Arguments cat_comp {A _ _ a b c} _ _.
Notation "g $o f" := (cat_comp g f).
Definition cat_postcomp {A} `{Is01Cat A} (a : A) {b c : A} (g : b $-> c)
  : (a $-> b) -> (a $-> c).
Admitted.
Definition cat_precomp {A} `{Is01Cat A} {a b : A} (c : A) (f : a $-> b)
  : (b $-> c) -> (a $-> c).
Admitted.

Class Is0Gpd (A : Type) `{Is01Cat A} :=
  { gpd_rev : forall {a b : A}, (a $-> b) -> (b $-> a) }.

Definition GpdHom {A} `{Is0Gpd A} (a b : A) := a $-> b.
Notation "a $== b" := (GpdHom a b).
Global Instance reflexive_GpdHom {A} `{Is0Gpd A}
  : Reflexive GpdHom.
Admitted.

Definition Hom_path {A : Type} `{Is01Cat A} {a b : A} (p : a = b) : (a $-> b).
Admitted.

Class Is0Functor {A B : Type} `{IsGraph A} `{IsGraph B} (F : A -> B)
  := { fmap : forall (a b : A) (f : a $-> b), F a $-> F b }.

Class Is2Graph (A : Type) `{IsGraph A}
  := isgraph_hom : forall (a b : A), IsGraph (a $-> b).
Global Existing Instance isgraph_hom | 20.

Class Is1Cat (A : Type) `{!IsGraph A, !Is2Graph A, !Is01Cat A} :=
{
  is01cat_hom : forall (a b : A), Is01Cat (a $-> b) ;
  is0gpd_hom : forall (a b : A), Is0Gpd (a $-> b) ;
  is0functor_postcomp : forall (a b c : A) (g : b $-> c), Is0Functor (cat_postcomp a g) ;
  is0functor_precomp : forall (a b c : A) (f : a $-> b), Is0Functor (cat_precomp c f) ;
  cat_assoc : forall (a b c d : A) (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f $== h $o (g $o f);
  cat_idl : forall (a b : A) (f : a $-> b), Id b $o f $== f;
  cat_idr : forall (a b : A) (f : a $-> b), f $o Id a $== f;
}.

Global Existing Instance is01cat_hom.
Global Existing Instance is0gpd_hom.

Class HasEquivs (A : Type) `{Is1Cat A} :=
{
  CatEquiv' : A -> A -> Type where "a $<~> b" := (CatEquiv' a b);
  CatIsEquiv' : forall a b, (a $-> b) -> Type;
  cate_fun' : forall a b, (a $<~> b) -> (a $-> b);
  cate_isequiv' : forall a b (f : a $<~> b), CatIsEquiv' a b (cate_fun' a b f);
  cate_buildequiv' : forall a b (f : a $-> b), CatIsEquiv' a b f -> CatEquiv' a b;
  cate_buildequiv_fun' : forall a b (f : a $-> b) (fe : CatIsEquiv' a b f),
      cate_fun' a b (cate_buildequiv' a b f fe) $== f;
  cate_inv' : forall a b (f : a $<~> b), b $-> a;
  cate_issect' : forall a b (f : a $<~> b),
    cate_inv' _ _ f $o cate_fun' _ _ f $== Id a;
  cate_isretr' : forall a b (f : a $<~> b),
      cate_fun' _ _ f $o cate_inv' _ _ f $== Id b;
  catie_adjointify' : forall a b (f : a $-> b) (g : b $-> a)
    (r : f $o g $== Id b) (s : g $o f $== Id a), CatIsEquiv' a b f;
}.

Definition CatEquiv {A} `{HasEquivs A} (a b : A)
  := @CatEquiv' A _ _ _ _ _ a b.

Notation "a $<~> b" := (CatEquiv a b).
Definition cate_fun {A} `{HasEquivs A} {a b : A} (f : a $<~> b)
  : a $-> b.
exact (@cate_fun' A _ _ _ _ _ a b f).
Defined.

Coercion cate_fun : CatEquiv >-> Hom.
Definition cate_adjointify {A} `{HasEquivs A} {a b : A}
           (f : a $-> b) (g : b $-> a)
           (r : f $o g $== Id b) (s : g $o f $== Id a)
  : a $<~> b.
Admitted.

Class Cat_IsBiInv {A} `{Is1Cat A} {x y : A} (f : x $-> y) := {
  cat_equiv_inv : y $-> x;
  cat_eisretr : f $o cat_equiv_inv $== Id y;
  cat_equiv_inv' : y $-> x;
  cat_eissect' : cat_equiv_inv' $o f $== Id x;
}.

Arguments cat_equiv_inv {A}%type_scope { _ _ _ _ x y} f {_}.

Arguments Build_Cat_IsBiInv {A}%type_scope {_ _ _ _ x y f} cat_equiv_inv cat_eisretr cat_equiv_inv' cat_eissect'.

Record Cat_BiInv A `{Is1Cat A} (x y : A) := {
  cat_equiv_fun :> x $-> y;
  cat_equiv_isequiv : Cat_IsBiInv cat_equiv_fun;
}.

Global Existing Instance cat_equiv_isequiv.
Definition cat_eissect {A} `{Is1Cat A} {x y : A} (f : x $-> y) {bif : Cat_IsBiInv f}
  : cat_equiv_inv f $o f $== Id x.
Admitted.

Definition cat_hasequivs A `{Is1Cat A} : HasEquivs A.
Proof.
  srapply Build_HasEquivs; intros x y.
  1: exact (Cat_BiInv _ x y).
  all:intros f;cbn beta in *. (* HERE *)
  -
 exact (Cat_IsBiInv f).
  -
 exact f.
  -
 exact _.
  -
 apply Build_Cat_BiInv.
  -
 intros; reflexivity.
  -
 exact (cat_equiv_inv f).
  -
 apply cat_eissect.
  -
 apply cat_eisretr.
  -
 intros g r s.
    exact (Build_Cat_IsBiInv g r g s).
Defined.

Global Instance isgraph_forall (A : Type) (B : A -> Type)
  `{forall a, IsGraph (B a)}
  : IsGraph (forall a, B a).
Proof.
  srapply Build_IsGraph.
  intros x y; exact (forall (a : A), x a $-> y a).
Defined.

Global Instance is01cat_forall (A : Type) (B : A -> Type)
  `{forall a, IsGraph (B a)} `{forall a, Is01Cat (B a)}
  : Is01Cat (forall a, B a).
Admitted.

Global Instance is0gpd_forall (A : Type) (B : A -> Type)

  `{forall a, IsGraph (B a)} `{forall a, Is01Cat (B a)} `{forall a, Is0Gpd (B a)}
  : Is0Gpd (forall a, B a).
Admitted.

Record ZeroGpd := {
  carrier :> Type;
  isgraph_carrier : IsGraph carrier;
  is01cat_carrier : Is01Cat carrier;
  is0gpd_carrier : Is0Gpd carrier;
}.

Global Existing Instance isgraph_carrier.
Global Existing Instance is01cat_carrier.
Global Existing Instance is0gpd_carrier.

Record Morphism_0Gpd (G H : ZeroGpd) := {
  fun_0gpd :> carrier G -> carrier H;
  is0functor_fun_0gpd : Is0Functor fun_0gpd;
}.

Global Instance isgraph_0gpd : IsGraph ZeroGpd.
Proof.
  apply Build_IsGraph.
  exact Morphism_0Gpd.
Defined.

Global Instance is01cat_0gpd : Is01Cat ZeroGpd.
Admitted.

Global Instance is2graph_0gpd : Is2Graph ZeroGpd.
Admitted.

Global Instance is1cat_0gpd : Is1Cat ZeroGpd.
Admitted.
Lemma hasequivs_0gpd : HasEquivs ZeroGpd.
exact (cat_hasequivs ZeroGpd).
Defined.

Definition prod_0gpd (I : Type) (G : I -> ZeroGpd) : ZeroGpd.
Proof.
  rapply (Build_ZeroGpd (forall i, G i)).
Defined.



Lemma foo:
  forall (I J : Type) (ie : Equiv I J) (G : forall _ : I, ZeroGpd) (H : forall _ : J, ZeroGpd)
    (f : forall i : I,
        @CatEquiv ZeroGpd isgraph_0gpd is2graph_0gpd is01cat_0gpd is1cat_0gpd hasequivs_0gpd
          (G i) (H (equiv_fun I J ie i))) (g h : carrier (prod_0gpd I G))
    (_ : @Hom (carrier (prod_0gpd I G)) (isgraph_carrier (prod_0gpd I G)) g h)
    (j : J),
    @Hom (carrier (H (equiv_fun I J ie (@equiv_inv I J (equiv_fun I J ie) (equiv_isequiv I J ie) j))))
      (isgraph_carrier
         (H (equiv_fun I J ie (@equiv_inv I J (equiv_fun I J ie) (equiv_isequiv I J ie) j))))
      (fun_0gpd (G (@equiv_inv I J (equiv_fun I J ie) (equiv_isequiv I J ie) j))
         (H (equiv_fun I J ie (@equiv_inv I J (equiv_fun I J ie) (equiv_isequiv I J ie) j)))
         (@cate_fun ZeroGpd isgraph_0gpd is2graph_0gpd is01cat_0gpd is1cat_0gpd hasequivs_0gpd
            (G (@equiv_inv I J (equiv_fun I J ie) (equiv_isequiv I J ie) j))
            (H (equiv_fun I J ie (@equiv_inv I J (equiv_fun I J ie) (equiv_isequiv I J ie) j)))
            (f (@equiv_inv I J (equiv_fun I J ie) (equiv_isequiv I J ie) j)))
         (g (@equiv_inv I J (equiv_fun I J ie) (equiv_isequiv I J ie) j)))
      (@transport J (fun x : J => carrier (H x))
         (equiv_fun I J ie (@equiv_inv I J (equiv_fun I J ie) (equiv_isequiv I J ie) j))
         (equiv_fun I J ie (@equiv_inv I J (equiv_fun I J ie) (equiv_isequiv I J ie) j))
         (@idpath J (equiv_fun I J ie (@equiv_inv I J (equiv_fun I J ie) (equiv_isequiv I J ie) j)))
         (fun_0gpd (G (@equiv_inv I J (equiv_fun I J ie) (equiv_isequiv I J ie) j))
            (H (equiv_fun I J ie (@equiv_inv I J (equiv_fun I J ie) (equiv_isequiv I J ie) j)))
            (@cate_fun ZeroGpd isgraph_0gpd is2graph_0gpd is01cat_0gpd is1cat_0gpd hasequivs_0gpd
               (G (@equiv_inv I J (equiv_fun I J ie) (equiv_isequiv I J ie) j))
               (H (equiv_fun I J ie (@equiv_inv I J (equiv_fun I J ie) (equiv_isequiv I J ie) j)))
               (f (@equiv_inv I J (equiv_fun I J ie) (equiv_isequiv I J ie) j)))
            (h (@equiv_inv I J (equiv_fun I J ie) (equiv_isequiv I J ie) j)))).
Proof.
  intros I J ie G H f g h p j.

  apply Build_Morphism_0Gpd.
Abort.
