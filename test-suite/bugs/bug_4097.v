Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 6082 lines to 81 lines, then from 436 lines to 93 lines *)
(* coqc version 8.5beta1 (February 2015) compiled on Feb 27 2015 15:10:37 with OCaml 4.01.0
   coqtop version cagnode15:/afs/csail.mit.edu/u/j/jgross/coq-8.5,v8.5 (fc1b3ef9d7270938cd83c524aae0383093b7a4b5) *)
Global Set Primitive Projections.
Record sigT {A} (P : A -> Type) := exist { projT1 : A ; projT2 : P projT1 }.
Arguments projT1 {A P} _ / .
Arguments projT2 {A P} _ / .
Notation "{ x : A  & P }" := (sigT (fun x:A => P)) : type_scope.
Delimit Scope path_scope with path.
Delimit Scope fibration_scope with fibration.
Open Scope path_scope.
Open Scope fibration_scope.
Notation "( x ; y )" := (exist _ _ x y) : fibration_scope.
Notation pr1 := projT1.
Notation pr2 := projT2.
Notation "x .1" := (pr1 x) (at level 3, format "x '.1'") : fibration_scope.
Notation "x .2" := (pr2 x) (at level 3, format "x '.2'") : fibration_scope.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a.
Arguments idpath {A a} , [A] a.
Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.
Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.
Notation "p @ q" := (concat p%path q%path) (at level 20) : path_scope.
Notation "p ^" := (inverse p%path) (at level 3, format "p '^'") : path_scope.
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.
Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.
Definition apD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x=y):
  p # (f x) = f y
  :=
  match p with idpath => idpath end.
Lemma transport_compose {A B} {x y : A} (P : B -> Type) (f : A -> B)
  (p : x = y) (z : P (f x))
  : transport (fun x => P (f x)) p z  =  transport P (ap f p) z.
admit.
Defined.
Generalizable Variables X A B C f g n.
Definition pr1_path `{P : A -> Type} {u v : sigT P} (p : u = v)
: u.1 = v.1
  := ap pr1 p.
Notation "p ..1" := (pr1_path p) (at level 3) : fibration_scope.
Definition pr2_path `{P : A -> Type} {u v : sigT P} (p : u = v)
: p..1 # u.2 = v.2
  := (transport_compose P pr1 p u.2)^
     @ (@apD {x:A & P x} _ pr2 _ _ p).
Notation "p ..2" := (pr2_path p) (at level 3) : fibration_scope.
Definition path_path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
           (p q : u = v)
           (rs : {r : p..1 = q..1 & transport (fun x => transport P x u.2 = v.2) r p..2 = q..2})
: p = q.
admit.
Defined.
Set Debug Unification.
Definition path_path_sigma {A : Type} (P : A -> Type) (u v : sigT P)
           (p q : u = v)
           (r : p..1 = q..1)
           (s : transport (fun x => transport P x u.2 = v.2) r p..2 = q..2)
: p = q
  := path_path_sigma_uncurried P u v p q (r; s).
