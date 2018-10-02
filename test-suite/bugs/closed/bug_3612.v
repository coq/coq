(* -*- mode: coq; coq-prog-args: ("-indices-matter" "-nois") -*- *)
(* File reduced by coq-bug-finder from original input, then from 3595 lines to 3518 lines, then from 3133 lines to 2950 lines, then from 2911 lines to 415 lines, then from 431 lines to 407 \
lines, then from 421 lines to 428 lines, then from 444 lines to 429 lines, then from 434 lines to 66 lines, then from 163 lines to 48 lines *)
(* coqc version trunk (September 2014) compiled on Sep 11 2014 14:48:8 with OCaml 4.01.0
   coqtop version cagnode17:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (580b25e05c7cc9e7a31430b3d9edb14ae12b7598) *)
Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x = y  :>  T" (at level 70, y at next level, no associativity).
Reserved Notation "x = y" (at level 70, no associativity).
Delimit Scope type_scope with type.
Bind Scope type_scope with Sortclass.
Open Scope type_scope.
Global Set Universe Polymorphism.
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Generalizable All Variables.
Local Set Primitive Projections.
Record sigT {A} (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.
Arguments projT1 {A P} _ / .
Arguments projT2 {A P} _ / .
Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Open Scope fibration_scope.
Notation pr1 := projT1.
Notation pr2 := projT2.
Notation "x .1" := (pr1 x) (at level 3, format "x '.1'") : fibration_scope.
Notation "x .2" := (pr2 x) (at level 3, format "x '.2'") : fibration_scope.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a.
Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Axiom transport : forall {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x), P y .
Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.
Local Open Scope path_scope.
Axiom pr1_path : forall `{P : A -> Type} {u v : sigT P} (p : u = v), u.1 = v.1.
Notation "p ..1" := (pr1_path p) (at level 3) : fibration_scope.
Axiom pr2_path : forall `{P : A -> Type} {u v : sigT P} (p : u = v), p..1 # u.2 = v.2.
Notation "p ..2" := (pr2_path p) (at level 3) : fibration_scope.
Axiom path_path_sigma : forall {A : Type} (P : A -> Type) (u v : sigT P)
           (p q : u = v)
           (r : p..1 = q..1)
           (s : transport (fun x => transport P x u.2 = v.2) r p..2 = q..2),
p = q.

Declare ML Module "ltac_plugin".

Set Default Proof Mode "Classic".

Goal forall (A : Type) (B : forall _ : A, Type) (x : @sigT A (fun x : A => B x))
            (xx : @paths (@sigT A (fun x0 : A => B x0)) x x),
       @paths (@paths (@sigT A (fun x0 : A => B x0)) x x) xx
              (@idpath (@sigT A (fun x0 : A => B x0)) x).
  intros A B x xx.
  Set Printing All.
  change (fun x => B x) with B in xx.
  pose (path_path_sigma B x x xx) as x''.
  clear x''.
  Check (path_path_sigma B x x xx).
