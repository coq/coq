Set Primitive Projections.
Set Implicit Arguments.

Record prod {A} {B}:= pair { fst : A ; snd : B }.
Notation " A * B " := (@prod A B) : type_scope.
Record sigT {A} (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.
Notation pr1 := (@projT1 _ _).
Arguments prod : clear implicits.

Check (@projT1 _ (fun x : nat => x = x)).
Check (fun s : @sigT nat (fun x : nat => x = x) => s.(projT1)).

Record rimpl {b : bool} {n : nat} := { foo : forall {x : nat}, x = n }. 

Check (fun r : @rimpl true 0 => r.(foo) (x:=0)).
Check (fun r : @rimpl true 0 => @foo true 0 r 0).
Check (fun r : @rimpl true 0 => foo r (x:=0)).
Check (fun r : @rimpl true 0 => @foo _ _ r 0).
Check (fun r : @rimpl true 0 => r.(@foo _ _)).
Check (fun r : @rimpl true 0 => r.(foo)).

Notation "{ x : T  & P }" := (@sigT T P).
Notation "{ x : A  & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
(* Notation "{ x : T * U  & P }" := (@sigT (T * U) P). *)

Definition compose {A B C : Type} (g : B -> C) (f : A -> B) := fun x => g (f x).
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Arguments idpath {A a} , [A] a.
Class IsEquiv {A B : Type} (f : A -> B) := {}.

Local Instance isequiv_tgt_compose A B
: @IsEquiv (A -> {xy : B * B & fst xy = snd xy})
           (A -> B)
           (@compose A {xy : B * B & fst xy = snd xy} B
                     (@compose {xy : B * B & fst xy = snd xy} _ B (@snd B B) pr1)).
(* Toplevel input, characters 220-223: *)
(* Error: Cannot infer this placeholder. *)

Local Instance isequiv_tgt_compose' A B
: @IsEquiv (A -> {xy : B * B & fst xy = snd xy})
           (A -> B)
           (@compose A {xy : B * B & fst xy = snd xy} B (@compose {xy : B * B & fst xy = snd xy} _ B (@snd _ _) pr1)).
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
           (@compose A {xy : B * B & fst xy = snd xy} B (@compose {xy : B * B & fst xy = snd xy} _ B (@snd _ _) 
                                                                  (fun s => s.(projT1)))).
(* Toplevel input, characters 15-241:
Error:
Cannot infer an internal placeholder of type "Type" in environment:

A : Type
B : Type
x : ?32
. *)
