(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Natural numbers [nat] built from [O] and [S] are defined in Datatypes.v *)

(** This module defines the following operations on natural numbers :
    - predecessor [pred]
    - addition [plus]
    - multiplication [mult]
    - less or equal order [le]
    - less [lt]
    - greater or equal [ge]
    - greater [gt]

   This module states various lemmas and theorems about natural numbers,
   including Peano's axioms of arithmetic (in Coq, these are in fact provable)
   Case analysis on [nat] and induction on [nat * nat] are provided too *)

Require Notations.
Require Datatypes.
Require Logic.

Open Scope nat_scope.

Definition eq_S := (f_equal nat nat S).

Hint eq_S : v62 := Resolve (f_equal nat nat S).
Hint eq_nat_unary : core := Resolve (f_equal nat).

(** The predecessor function *)

Definition pred : nat->nat := [n:nat](Cases n of O => O | (S u) => u end).
Hint eq_pred : v62 := Resolve (f_equal nat nat pred).

Theorem pred_Sn : (m:nat) m=(pred (S m)).
Proof.
  Auto.
Qed.

Theorem eq_add_S : (n,m:nat) (S n)=(S m) -> n=m.
Proof.
  Intros n m H ; Change (pred (S n))=(pred (S m)); Auto.
Qed.

Hints Immediate eq_add_S : core v62.

(** A consequence of the previous axioms *)

Theorem not_eq_S : (n,m:nat) ~(n=m) -> ~((S n)=(S m)).
Proof.
  Red; Auto.
Qed.
Hints Resolve not_eq_S : core v62.

Definition IsSucc : nat->Prop
  := [n:nat]Cases n of O => False | (S p) => True end.


Theorem O_S : (n:nat)~(O=(S n)).
Proof.
  Red;Intros n H.
  Change (IsSucc O).
  Rewrite <- (sym_eq nat O (S n));[Exact I | Assumption].
Qed.
Hints Resolve O_S : core v62.

Theorem n_Sn : (n:nat) ~(n=(S n)).
Proof.
  NewInduction n ; Auto.
Qed.
Hints Resolve n_Sn : core v62.

(** Addition *)

Fixpoint plus [n:nat] : nat -> nat := 
   [m:nat]Cases n of 
      O   => m 
  | (S p) => (S (plus p m)) end.
Hint eq_plus : v62 := Resolve (f_equal2 nat nat nat plus).
Hint eq_nat_binary : core := Resolve (f_equal2 nat nat).

V8Infix "+" plus : nat_scope.

Lemma plus_n_O : (n:nat) n=(plus n O).
Proof.
  NewInduction n ; Simpl ; Auto.
Qed.
Hints Resolve plus_n_O : core v62.

Lemma plus_O_n : (n:nat) (plus O n)=n.
Proof.
  Auto.
Qed.

Lemma plus_n_Sm : (n,m:nat) (S (plus n m))=(plus n (S m)).
Proof.
  Intros n m; NewInduction n; Simpl; Auto.
Qed.
Hints Resolve plus_n_Sm : core v62.

Lemma plus_Sn_m : (n,m:nat)(plus (S n) m)=(S (plus n m)).
Proof.
  Auto.
Qed.

(** Multiplication *)

Fixpoint  mult [n:nat] : nat -> nat := 
   [m:nat]Cases n of O => O 
               | (S p) => (plus m (mult p m)) end.
Hint eq_mult : core v62 := Resolve (f_equal2 nat nat nat mult).

V8Infix "*" mult : nat_scope.

Lemma mult_n_O : (n:nat) O=(mult n O).
Proof.
  NewInduction n; Simpl; Auto.
Qed.
Hints Resolve mult_n_O : core v62.

Lemma mult_n_Sm : (n,m:nat) (plus (mult n m) n)=(mult n (S m)).
Proof.
  Intros; NewInduction n as [|p H]; Simpl; Auto.
  NewDestruct H; Rewrite <- plus_n_Sm; Apply (f_equal nat nat S).
  Pattern 1 3 m; Elim m; Simpl; Auto.
Qed.
Hints Resolve mult_n_Sm : core v62.

(** Definition of subtraction on [nat] : [m-n] is [0] if [n>=m] *)

Fixpoint minus [n:nat] : nat -> nat := 
  [m:nat]Cases n m of
            O    _     =>  O
         | (S k) O     => (S k)
         | (S k) (S l) => (minus k l)
        end. 

V8Infix "-" minus : nat_scope.

(** Definition of the usual orders, the basic properties of [le] and [lt] 
    can be found in files Le and Lt *)

(** An inductive definition to define the order *)

Inductive le [n:nat] : nat -> Prop
    := le_n : (le n n)
     | le_S : (m:nat)(le n m)->(le n (S m)).

V8Infix "<=" le : nat_scope.

Hint constr_le : core v62 := Constructors le.
(*i equivalent to : "Hints Resolve le_n le_S : core v62." i*)

Definition lt := [n,m:nat](le (S n) m).
Hints Unfold lt : core v62.

V8Infix "<" lt : nat_scope.

Definition ge := [n,m:nat](le m n).
Hints Unfold ge : core v62.

V8Infix ">=" ge : nat_scope.

Definition gt := [n,m:nat](lt m n).
Hints Unfold gt : core v62.

V8Infix ">" gt : nat_scope.

V8Notation "x <= y <= z" := (le x y)/\(le y z) : nat_scope.
V8Notation "x <= y < z"  := (le x y)/\(lt y z) : nat_scope.
V8Notation "x < y < z"   := (lt x y)/\(lt y z) : nat_scope.
V8Notation "x < y <= z"  := (lt x y)/\(le y z) : nat_scope.

(** Pattern-Matching on natural numbers *)

Theorem nat_case : (n:nat)(P:nat->Prop)(P O)->((m:nat)(P (S m)))->(P n).
Proof.
  NewInduction n ; Auto.
Qed.

(** Principle of double induction *)

Theorem nat_double_ind : (R:nat->nat->Prop)
     ((n:nat)(R O n)) -> ((n:nat)(R (S n) O))
     -> ((n,m:nat)(R n m)->(R (S n) (S m)))
     -> (n,m:nat)(R n m).
Proof.
  NewInduction n; Auto.
  NewDestruct m; Auto.
Qed.

(** Notations *)
V7only[
Syntax constr
  level 0:
    S [ (S $p) ] -> [$p:"nat_printer":9]
  | O [ O ]      -> ["(0)"].
].

V7only [
(* For parsing/printing based on scopes *)
Module nat_scope.
Infix 4 "+" plus : nat_scope.
Infix 3 "*" mult : nat_scope.
Infix 4 "-" minus : nat_scope.
Infix NONA 5 "<=" le : nat_scope.
Infix NONA 5 "<" lt : nat_scope.
Infix NONA 5 ">=" ge : nat_scope.
Infix NONA 5 ">" gt : nat_scope.
End nat_scope.
].
