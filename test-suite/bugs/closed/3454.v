
(* File reduced by coq-bug-finder from original input, then from 5135 lines to 4962 lines, then from 4444 lines to 100 lines, then from 106 lines to 97 lines, then from 105 lines to 28 lines *)

Set Primitive Projections.

Class Identity {A} (Hom : A -> A -> Type) :=
  { identity : forall x, Hom x x }.

Instance eqaid A : Identity (@eq A) :=
  { identity x := eq_refl }.

Check (identity 0).

Record sigT {A} (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.
Notation pr1 := (@projT1 _ _).
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) := fun x => g (f x).
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Arguments idpath {A a} , [A] a.
Class IsEquiv {A B : Type} (f : A -> B) := {}.


Notation pr1' x := (x.(projT1)).


Notation "{ x : A & P }" := (@sigT A (fun x => P)) : type_scope.
Local Instance isequiv_tgt_compose A B
: @IsEquiv (A -> {xy : B * B & fst xy = snd xy})
           (A -> B)
           (@compose A {xy : B * B & fst xy = snd xy} B (@compose {xy : B * B & fst xy = snd xy} _ B (@snd B B) pr1)).

Local Instance isequiv_tgt_compose' A B
: @IsEquiv (A -> {xy : B * B & fst xy = snd xy})
           (A -> B)
           (@compose A {xy : B * B & fst xy = snd xy} B (@compose {xy : B * B & fst xy = snd xy} _ B (@snd B B) (fun x => pr1' x))).

(* Toplevel input, characters 220-223: *)
(* Error: Cannot infer this placeholder. *)

Local Instance isequiv_tgt_compose''' A B
: @IsEquiv (A -> {xy : B * B & fst xy = snd xy})
           (A -> B)
           (@compose A {xy : B * B & fst xy = snd xy} B (@compose {xy : B * B & fst xy = snd xy} _ B (@snd _ _) (@projT1 _ _))).
(* Toplevel input, characters 221-232: *)
(* Error: *)
(* In environment *)
(* A : Type *)
(* B : Type *)
(* The term "pr1" has type "sigT ?30 -> ?29" while it is expected to have type *)
(*  "{xy : B * B & fst xy = snd xy} -> ?27 * B". *)

Local Instance isequiv_tgt_compose'' A B
: @IsEquiv (A -> {xy : B * B & fst xy = snd xy})
           (A -> B)
           (@compose A {xy : B * B & fst xy = snd xy} B (@compose {xy : B * B & fst xy = snd xy} _ B (@snd _ _) pr1)).
(* Toplevel input, characters 15-241:
Error:
Cannot infer an internal placeholder of type "Type" in environment:

A : Type
B : Type
x : ?32
. *)