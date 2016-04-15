(* Testing 8.5 regression with type classes not solving evars 
   redefined while trying to solve them with the type class mechanism *)

Global Set Universe Polymorphism.
Monomorphic Universe i.
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.
Arguments idpath {A a} , [A] a.
Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.
Notation "-1" := (trunc_S minus_two) (at level 0).

Class IsPointed (A : Type) := point : A.
Arguments point A {_}.

Record pType :=
  { pointed_type : Type ;
    ispointed_type : IsPointed pointed_type }.
Coercion pointed_type : pType >-> Sortclass.
Existing Instance ispointed_type.

Private Inductive Trunc (n : trunc_index) (A :Type) : Type :=
  tr : A -> Trunc n A.
Arguments tr {n A} a.



Record ooGroup :=
  { classifying_space : pType@{i} }.

Definition group_loops (X : pType)
: ooGroup.
Proof.
  (** This works: *)
  pose (x0 := point X).
  pose (H := existT (fun x:X => Trunc -1 (x = point X)) x0 (tr idpath)).
  clear H x0.
  (** But this doesn't: *)
  pose (existT (fun x:X => Trunc -1 (x = point X)) (point X) (tr idpath)).
