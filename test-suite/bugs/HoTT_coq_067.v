Require Import TestSuite.admit.
Set Universe Polymorphism.
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Goal forall (A : Type) (P : forall _ : A, Type) (x0 : A)
     (p : P x0) (q : @paths (@sigT A P) (@existT A P x0 p) (@existT A P x0 p)),
   @paths (@paths (@sigT A P) (@existT A P x0 p) (@existT A P x0 p))
     (@idpath (@sigT A P) (@existT A P x0 p))
     (@idpath (@sigT A P) (@existT A P x0 p)).
  intros.
  induction q.
  admit.
Qed.
(** Error: Illegal application:
The term "paths_rect" of type
 "forall (A : Type) (a : A) (P : forall a0 : A, paths a a0 -> Type),
  P a (idpath a) -> forall (y : A) (p : paths a y), P y p"
cannot be applied to the terms
 "{x : _ & P x}" : "Type"
 "s" : "{x : _ & P x}"
 "fun (a : {x : _ & P x}) (_ : paths s a) => paths (idpath a) (idpath a)"
   : "forall a : {x : _ & P x}, paths s a -> Type"
 "match proof_admitted return (paths (idpath s) (idpath s)) with
  end" : "paths (idpath s) (idpath s)"
 "s" : "{x : _ & P x}"
 "q" : "paths (existT P x0 p) (existT P x0 p)"
The 3rd term has type "forall a : {x : _ & P x}, paths s a -> Type"
which should be coercible to "forall a : {x : _ & P x}, paths s a -> Type". *)
