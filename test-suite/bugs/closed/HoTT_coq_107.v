(* -*- mode: coq; coq-prog-args: ("-nois" "-R" "../theories" "Coq") -*- *)
(* File reduced by coq-bug-finder from 4897 lines to 2605 lines, then from 2297 lines to 236 lines, then from 239 lines to 137 lines, then from 118 lines to 67 lines, then from 520 lines to 76 lines. *)
(** Note: The bug here is the same as the #113, that is, HoTT_coq_113.v *)
Require Import Coq.Init.Logic.
Global Set Universe Polymorphism.
Global Set Asymmetric Patterns.
Set Implicit Arguments.

Inductive sigT (A:Type) (P:A -> Type) : Type :=
  existT : forall x:A, P x -> sigT P.

Notation "{ x : A  & P }" := (sigT (fun x:A => P)) : type_scope.

Generalizable All Variables.
Definition admit {T} : T.
Admitted.
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.
Class Contr_internal (A : Type) :=
  BuildContr {
      center : A ;
      contr : (forall y : A, center = y)
    }.

Arguments center A {_}.

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | minus_two => Contr_internal A
    | trunc_S n' => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.

Notation Contr := (IsTrunc minus_two).

Hint Extern 0 => progress change Contr_internal with Contr in * : typeclass_instances.

Definition path_contr `{Contr A} (x y : A) : x = y
  := admit.

Definition path_sigma' {A : Type} (P : A -> Type) {x x' : A} {y : P x} {y' : P x'}
           (p : x = x') (q : transport _ p y = y')
: existT _ x y = existT _ x' y'
  := admit.
Instance trunc_sigma `{P : A -> Type}
         `{IsTrunc n A} `{forall a, IsTrunc n (P a)}
: IsTrunc n (sigT P) | 100.

Proof.
  generalize dependent A.
  induction n; [ | apply admit ]; simpl; intros A P ac Pc.
  (exists (existT _ (center A) (center (P (center A))))).
  intros [a ?].
  refine (path_sigma' P (contr a) (path_contr _ _)).
Defined.
Inductive Bool : Set := true | false.
Definition trunc_sum' n A B `{IsTrunc n Bool, IsTrunc n A, IsTrunc n B}
: (IsTrunc n { b : Bool & if b then A else B }).
Proof.
  Set Printing All.
  Set Printing Universes.
  refine (@trunc_sigma Bool (fun b => if b then A else B) n _ _).
  (* Toplevel input, characters 23-76:
Error:
In environment
n : trunc_index
A : Type (* Top.193 *)
B : Type (* Top.194 *)
H : IsTrunc (* Set *) n Bool
H0 : IsTrunc (* Top.193 *) n A
H1 : IsTrunc (* Top.194 *) n B
The term
 "@trunc_sigma (* Top.198 Top.199 Top.200 Top.201 *) Bool
    (fun b : Bool =>
     match b return Type (* Top.199 *) with
     | true => A
     | false => B
     end) n ?49 ?50" has type
 "IsTrunc (* Top.200 *) n
    (@sig (* Top.199 Top.199 *) Bool
       (fun b : Bool =>
        match b return Type (* Top.199 *) with
        | true => A
        | false => B
        end))" while it is expected to have type
 "IsTrunc (* Top.195 *) n
    (@sig (* Set Top.197 *) Bool
       (fun b : Bool =>
        match b return Type (* Top.197 *) with
        | true => A
        | false => B
        end))" (Universe inconsistency: Cannot enforce Top.197 = Set)).
 *)
  apply admit.
Defined.
