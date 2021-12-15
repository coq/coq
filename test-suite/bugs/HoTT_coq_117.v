(* File reduced by coq-bug-finder from original input, then from 1461 lines to 81 lines, then from 84 lines to 40 lines, then from 50 lines to 24 lines *)

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.
Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Class Contr_internal (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.
Class Funext := {}.

Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) :
  (forall x, f x = g x) -> f = g.

Admitted.

Inductive Empty : Set := .
Fail Instance contr_from_Empty {_ : Funext} (A : Type) :
  Contr_internal (Empty -> A) :=
  BuildContr _
             (Empty_rect (fun _ => A))
             (fun f => path_forall _ f (fun x => Empty_rect _ x)).

Fail Instance contr_from_Empty {F : Funext} (A : Type) :
  Contr_internal (Empty -> A) :=
  BuildContr _
             (Empty_rect (fun _ => A))
             (fun f => path_forall _ f (fun x => Empty_rect _ x)).

(** This could be disallowed, this uses the Funext argument *)
Instance contr_from_Empty {_ : Funext} (A : Type) :
  Contr_internal (Empty -> A) :=
  BuildContr _
             (Empty_rect (fun _ => A))
             (fun f => path_forall _ f (fun x => Empty_rect (fun _ => _ x = f x) x)).

Instance contr_from_Empty' {_ : Funext} (A : Type) :
  Contr_internal (Empty -> A) :=
  BuildContr _
             (Empty_rect (fun _ => A))
             (fun f => path_forall _ f (fun x => Empty_rect (fun _ => _ x = f x) x)).
(* Toplevel input, characters 15-220:
Anomaly: unknown meta ?190. Please report. *)
