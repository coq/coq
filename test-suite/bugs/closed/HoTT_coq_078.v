Set Implicit Arguments.
Require Import Logic.

(*Global Set Universe Polymorphism.*)
Global Set Asymmetric Patterns.
Local Set Primitive Projections.

Local Open Scope type_scope.

Record prod (A B : Type) : Type :=
  pair { fst : A; snd : B }.

Arguments pair {A B} _ _.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Generalizable Variables X A B f g n.

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

Definition transport_prod' {A : Type} {P Q : A -> Type} {a a' : A} (p : a = a')
  (z : P a * Q a)
  : transport (fun a => P a * Q a) p z  =  (transport _ p (fst z), transport _ p (snd z))
  := match p as p' return transport (fun a0 => P a0 * Q a0) p' z = (transport P p' (fst z), transport Q p' (snd z)) with
       | idpath => idpath
     end. (* success *)

Definition transport_prod {A : Type} {P Q : A -> Type} {a a' : A} (p : a = a')
  (z : P a * Q a)
  : transport (fun a => P a * Q a) p z  =  (transport _ p (fst z), transport _ p (snd z))
  := match p with
       | idpath => idpath
     end.
