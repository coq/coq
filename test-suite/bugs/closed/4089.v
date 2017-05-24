Unset Strict Universe Declaration.
Require Import TestSuite.admit.
(* -*- mode: coq; coq-prog-args: ("-indices-matter") -*- *)
(* File reduced by coq-bug-finder from original input, then from 6522 lines to 318 lines, then from 1139 lines to 361 lines *)
(* coqc version 8.5beta1 (February 2015) compiled on Feb 23 2015 18:32:3 with OCaml 4.01.0
   coqtop version cagnode15:/afs/csail.mit.edu/u/j/jgross/coq-8.5,v8.5 (ebfc19d792492417b129063fb511aa423e9d9e08) *)
Open Scope type_scope.

Global Set Universe Polymorphism.
Module Export Datatypes.

Set Implicit Arguments.

Record prod (A B : Type) := pair { fst : A ; snd : B }.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

End Datatypes.
Module Export Specif.

Set Implicit Arguments.

Record sig {A} (P : A -> Type) := exist { proj1_sig : A ; proj2_sig : P proj1_sig }.

Notation sigT := sig (only parsing).
Notation existT := exist (only parsing).

Notation "{ x : A  & P }" := (sigT (fun x:A => P)) : type_scope.

Notation projT1 := proj1_sig (only parsing).
Notation projT2 := proj2_sig (only parsing).

End Specif.

Ltac rapply p :=
  refine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _) ||
  refine (p _ _ _ _ _) ||
  refine (p _ _ _ _) ||
  refine (p _ _ _) ||
  refine (p _ _) ||
  refine (p _) ||
  refine p.

Local Unset Elimination Schemes.

Definition relation (A : Type) := A -> A -> Type.

Class Symmetric {A} (R : relation A) :=
  symmetry : forall x y, R x y -> R y x.

Class Transitive {A} (R : relation A) :=
  transitivity : forall x y z, R x y -> R y z -> R x z.

Tactic Notation "etransitivity" open_constr(y) :=
  let R := match goal with |- ?R ?x ?z => constr:(R) end in
  let x := match goal with |- ?R ?x ?z => constr:(x) end in
  let z := match goal with |- ?R ?x ?z => constr:(z) end in
  let pre_proof_term_head := constr:(@transitivity _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  refine (proof_term_head x y z _ _); [ change (R x y) | change (R y z) ].

Ltac transitivity x := etransitivity x.

Definition Type1 := Eval hnf in let gt := (Set : Type@{i}) in Type@{i}.

Notation idmap := (fun x => x).
Delimit Scope function_scope with function.
Delimit Scope path_scope with path.
Delimit Scope fibration_scope with fibration.
Open Scope fibration_scope.
Open Scope function_scope.

Notation "( x ; y )" := (existT _ x y) : fibration_scope.

Notation pr1 := projT1.
Notation pr2 := projT2.

Notation "x .1" := (pr1 x) (at level 3, format "x '.1'") : fibration_scope.
Notation "x .2" := (pr2 x) (at level 3, format "x '.2'") : fibration_scope.

Notation compose := (fun g f x => g (f x)).

Notation "g 'o' f" := (compose g%function f%function) (at level 40, left associativity) : function_scope.

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Scheme paths_ind := Induction for paths Sort Type.

Definition paths_rect := paths_ind.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Local Open Scope path_scope.

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.

Arguments concat {A x y z} p q : simpl nomatch.

Notation "1" := idpath : path_scope.

Notation "p @ q" := (concat p%path q%path) (at level 20) : path_scope.

Notation "p ^" := (inverse p%path) (at level 3, format "p '^'") : path_scope.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, f x = g x.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : f == g
  := fun x => match h with idpath => 1 end.

Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Arguments eisretr {A B}%type_scope f%function_scope {_} _.
Arguments eissect {A B}%type_scope f%function_scope {_} _.
Arguments eisadj {A B}%type_scope f%function_scope {_} _.

Record Equiv A B := BuildEquiv {
  equiv_fun : A -> B ;
  equiv_isequiv : IsEquiv equiv_fun
}.

Coercion equiv_fun : Equiv >-> Funclass.

Global Existing Instance equiv_isequiv.

Bind Scope equiv_scope with Equiv.

Notation "A <~> B" := (Equiv A B) (at level 85) : type_scope.

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'") : function_scope.

Inductive Unit : Set :=
    tt : Unit.

Ltac done :=
  trivial; intros; solve
    [ repeat first
      [ solve [trivial]
      | solve [symmetry; trivial]
      | reflexivity

      | contradiction
      | split ]
    | match goal with
      H : ~ _ |- _ => solve [destruct H; trivial]
      end ].
Tactic Notation "by" tactic(tac) :=
  tac; done.

Definition concat_p1 {A : Type} {x y : A} (p : x = y) :
  p @ 1 = p
  :=
  match p with idpath => 1 end.

Definition concat_1p {A : Type} {x y : A} (p : x = y) :
  1 @ p = p
  :=
  match p with idpath => 1 end.

Definition ap_pp {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p @ q) = (ap f p) @ (ap f q)
  :=
  match q with
    idpath =>
    match p with idpath => 1 end
  end.

Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (g o f) p = ap g (ap f p)
  :=
  match p with idpath => 1 end.

Definition concat_A1p {A : Type} {f : A -> A} (p : forall x, f x = x) {x y : A} (q : x = y) :
  (ap f q) @ (p y) = (p x) @ q
  :=
  match q with
    | idpath => concat_1p _ @ ((concat_p1 _) ^)
  end.

Definition concat2 {A} {x y z : A} {p p' : x = y} {q q' : y = z} (h : p = p') (h' : q = q')
  : p @ q = p' @ q'
:= match h, h' with idpath, idpath => 1 end.

Notation "p @@ q" := (concat2 p q)%path (at level 20) : path_scope.

Definition whiskerL {A : Type} {x y z : A} (p : x = y)
  {q r : y = z} (h : q = r) : p @ q = p @ r
:= 1 @@ h.

Definition ap02 {A B : Type} (f:A->B) {x y:A} {p q:x=y} (r:p=q) : ap f p = ap f q
  := match r with idpath => 1 end.
Module Export Equivalences.

Generalizable Variables A B C f g.

Global Instance isequiv_idmap (A : Type) : IsEquiv idmap | 0 :=
  BuildIsEquiv A A idmap idmap (fun _ => 1) (fun _ => 1) (fun _ => 1).

Definition equiv_idmap (A : Type) : A <~> A := BuildEquiv A A idmap _.

Arguments equiv_idmap {A} , A.

Notation "1" := equiv_idmap : equiv_scope.

Global Instance isequiv_compose `{IsEquiv A B f} `{IsEquiv B C g}
  : IsEquiv (compose g f) | 1000
  := BuildIsEquiv A C (compose g f)
    (compose f^-1 g^-1)
    (fun c => ap g (eisretr f (g^-1 c)) @ eisretr g c)
    (fun a => ap (f^-1) (eissect g (f a)) @ eissect f a)
    (fun a =>
      (whiskerL _ (eisadj g (f a))) @
      (ap_pp g _ _)^ @
      ap02 g
      ( (concat_A1p (eisretr f) (eissect g (f a)))^ @
        (ap_compose f^-1 f _ @@ eisadj f a) @
        (ap_pp f _ _)^
      ) @
      (ap_compose f g _)^
    ).

Definition equiv_compose {A B C : Type} (g : B -> C) (f : A -> B)
  `{IsEquiv B C g} `{IsEquiv A B f}
  : A <~> C
  := BuildEquiv A C (compose g f) _.

Global Instance transitive_equiv : Transitive Equiv | 0 :=
  fun _ _ _ f g => equiv_compose g f.

Theorem equiv_inverse {A B : Type} : (A <~> B) -> (B <~> A).
admit.
Defined.

Global Instance symmetric_equiv : Symmetric Equiv | 0 := @equiv_inverse.

End Equivalences.

Definition path_prod_uncurried {A B : Type} (z z' : A * B)
  (pq : (fst z = fst z') * (snd z = snd z'))
  : (z = z').
admit.
Defined.

Global Instance isequiv_path_prod {A B : Type} {z z' : A * B}
: IsEquiv (path_prod_uncurried z z') | 0.
admit.
Defined.

Definition equiv_path_prod {A B : Type} (z z' : A * B)
  : (fst z = fst z') * (snd z = snd z')  <~>  (z = z')
  := BuildEquiv _ _ (path_prod_uncurried z z') _.

Generalizable Variables X A B C f g n.

Definition functor_sigma `{P : A -> Type} `{Q : B -> Type}
           (f : A -> B) (g : forall a, P a -> Q (f a))
: sigT P -> sigT Q
  := fun u => (f u.1 ; g u.1 u.2).

Global Instance isequiv_functor_sigma `{P : A -> Type} `{Q : B -> Type}
         `{IsEquiv A B f} `{forall a, @IsEquiv (P a) (Q (f a)) (g a)}
: IsEquiv (functor_sigma f g) | 1000.
admit.
Defined.

Definition equiv_functor_sigma `{P : A -> Type} `{Q : B -> Type}
           (f : A -> B) `{IsEquiv A B f}
           (g : forall a, P a -> Q (f a))
           `{forall a, @IsEquiv (P a) (Q (f a)) (g a)}
: sigT P <~> sigT Q
  := BuildEquiv _ _ (functor_sigma f g) _.

Definition equiv_functor_sigma' `{P : A -> Type} `{Q : B -> Type}
           (f : A <~> B)
           (g : forall a, P a <~> Q (f a))
: sigT P <~> sigT Q
  := equiv_functor_sigma f g.

Definition equiv_functor_sigma_id `{P : A -> Type} `{Q : A -> Type}
           (g : forall a, P a <~> Q a)
: sigT P <~> sigT Q
  := equiv_functor_sigma' 1 g.

Definition Bip : Type := { C : Type &  C * C }.

Definition BipMor (X Y : Bip) : Type :=
  match X, Y with (C;(c0,c1)), (D;(d0,d1)) =>
    { f : C -> D & (f c0 = d0) * (f c1 = d1) }
  end.

Definition bipmor2map {X Y : Bip} : BipMor X Y -> X.1 -> Y.1 :=
  match X, Y with (C;(c0,c1)), (D;(d0,d1)) => fun i =>
    match i with (f;_) => f end
  end.

Definition bipidmor {X : Bip} : BipMor X X :=
  match X with (C;(c0,c1)) => (idmap; (1, 1)) end.

Definition bipcompmor {X Y Z : Bip} : BipMor X Y -> BipMor Y Z -> BipMor X Z :=
  match X, Y, Z with (C;(c0,c1)), (D;(d0,d1)), (E;(e0,e1)) => fun i j =>
    match i, j with (f;(f0,f1)), (g;(g0,g1)) =>
      (g o f; (ap g f0 @ g0, ap g f1 @ g1))
    end
  end.

Definition isbipequiv {X Y : Bip} (i : BipMor X Y) : Type :=
  { l : BipMor Y X & bipcompmor i l = bipidmor } *
  { r : BipMor Y X & bipcompmor r i = bipidmor }.

Lemma bipequivEQequiv : forall {X Y : Bip} (i : BipMor X Y),
  isbipequiv i <~> IsEquiv (bipmor2map i).
Proof.
assert (equivcompmor : forall {X Y : Bip} (i : BipMor X Y) j,
(bipcompmor i j = bipidmor) <~> Unit).
  intros; set (U := X); set (V := Y); destruct X as [C [c0 c1]], Y as [D [d0 d1]].
  transitivity { n : (bipcompmor i j).1 = (@bipidmor U).1 &
  (bipcompmor i j).2 = transport (fun h => (h c0 = c0) * (h c1 = c1)) n^ (@bipidmor U).2}.
    admit.
  destruct i as [f [f0 f1]]; destruct j as [g [g0 g1]].

  transitivity { n : g o f = idmap & (ap g f0 @ g0 = apD10 n c0 @ 1) *
  (ap g f1 @ g1 = apD10 n c1 @ 1)}.
    apply equiv_functor_sigma_id; intro n.
    assert (Ggen : forall (h0 h1 : C -> C) (p : h0 = h1) u0 u1 v0 v1,
    ((u0, u1) = transport (fun h => (h c0 = c0) * (h c1 = c1)) p^ (v0, v1)) <~>
    (u0 = apD10 p c0 @ v0) * (u1 = apD10 p c1 @ v1)).
      induction p; intros; simpl; rewrite !concat_1p; apply symmetry.
      by apply (equiv_path_prod (u0,u1) (v0,v1)).
    rapply Ggen.
    pose (@paths C).
    Check (@paths C).
    Undo.
    Check (@paths C). (* Toplevel input, characters 0-17:
Error: Illegal application:
The term "@paths" of type "forall A : Type, A -> A -> Type"
cannot be applied to the term
 "C" : "Type"
This term has type "Type@{Top.892}" which should be coercible to
 "Type@{Top.882}".
*)
