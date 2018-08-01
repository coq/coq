(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Definitions of Vectors and functions to use them

   Author: Pierre Boutillier
   Institution: PPS, INRIA 12/2010
*)

(**
Names should be "caml name in list.ml" if exists and order of arguments
have to be the same. complain if you see mistakes ... *)

Require Import Arith_base.
Require Vectors.Fin.
Import EqNotations.
Local Open Scope nat_scope.

(* Set Universe Polymorphism. *)

(**
A vector is a list of size n whose elements belong to a set A. *)

Inductive t A : nat -> Type :=
  |nil : t A 0
  |cons : forall (h:A) (n:nat), t A n -> t A (S n).

Local Notation "[ ]" := (nil _) (format "[ ]").
Local Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

Section SCHEMES.

(** An induction scheme for non-empty vectors *)

Definition rectS {A} (P:forall {n}, t A (S n) -> Type)
 (bas: forall a: A, P (a :: []))
 (rect: forall a {n} (v: t A (S n)), P v -> P (a :: v)) :=
 fix rectS_fix {n} (v: t A (S n)) : P v :=
 match v with
 |@cons _ a 0 v =>
   match v with
     |nil _ => bas a
     |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
   end
 |@cons _ a (S nn') v => rect a v (rectS_fix v)
 |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
 end.

(** A vector of length [0] is [nil] *)
Definition case0 {A} (P:t A 0 -> Type) (H:P (nil A)) v:P v :=
match v with
  |[] => H
  |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
end.

(** A vector of length [S _] is [cons] *)
Definition caseS {A} (P : forall {n}, t A (S n) -> Type)
  (H : forall h {n} t, @P n (h :: t)) {n} (v: t A (S n)) : P v :=
match v with
  |h :: t => H h t
  |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
end.

Definition caseS' {A} {n : nat} (v : t A (S n)) : forall (P : t A (S n) -> Type)
  (H : forall h t, P (h :: t)), P v :=
  match v with
  | h :: t => fun P H => H h t
  | _ => fun devil => False_rect (@IDProp) devil
  end.

(** An induction scheme for 2 vectors of same length *)
Definition rect2 {A B} (P:forall {n}, t A n -> t B n -> Type)
  (bas : P [] []) (rect : forall {n v1 v2}, P v1 v2 ->
    forall a b, P (a :: v1) (b :: v2)) :=
  fix rect2_fix {n} (v1 : t A n) : forall v2 : t B n, P v1 v2 :=
  match v1 with
  | [] => fun v2 => case0 _ bas v2
  | @cons _ h1 n' t1 => fun v2 =>
    caseS' v2 (fun v2' => P (h1::t1) v2') (fun h2 t2 => rect (rect2_fix t1 t2) h1 h2)
  end.

End SCHEMES.

Section BASES.
(** The first element of a non empty vector *)
Definition hd {A} := @caseS _ (fun n v => A) (fun h n t => h).
Global Arguments hd {A} {n} v.

(** The last element of an non empty vector *)
Definition last {A} := @rectS _ (fun _ _ => A) (fun a => a) (fun _ _ _ H => H).
Global Arguments last {A} {n} v.

(** Build a vector of n{^ th} [a] *)
Definition const {A} (a:A) := nat_rect _ [] (fun n x => cons _ a n x).

(** The [p]{^ th} element of a vector of length [m].

Computational behavior of this function should be the same as
ocaml function. *)
Definition nth {A} :=
fix nth_fix {m} (v' : t A m) (p : Fin.t m) {struct v'} : A :=
match p in Fin.t m' return t A m' -> A with
 |Fin.F1 => caseS (fun n v' => A) (fun h n t => h)
 |Fin.FS p' => fun v => (caseS (fun n v' => Fin.t n -> A)
   (fun h n t p0 => nth_fix t p0) v) p'
end v'.

(** An equivalent definition of [nth]. *)
Definition nth_order {A} {n} (v: t A n) {p} (H: p < n) :=
(nth v (Fin.of_nat_lt H)).

(** Put [a] at the p{^ th} place of [v] *)
Fixpoint replace {A n} (v : t A n) (p: Fin.t n) (a : A) {struct p}: t A n :=
  match p with
  | @Fin.F1 k => fun v': t A (S k) => caseS' v' _ (fun h t => a :: t)
  | @Fin.FS k p' => fun v' : t A (S k) =>
    (caseS' v' (fun _ => t A (S k)) (fun h t => h :: (replace t p' a)))
  end v.

(** Version of replace with [lt] *)
Definition replace_order {A n} (v: t A n) {p} (H: p < n) :=
replace v (Fin.of_nat_lt H).

(** Remove the first element of a non empty vector *)
Definition tl {A} := @caseS _ (fun n v => t A n) (fun h n t => t).
Global Arguments tl {A} {n} v.

(** Remove last element of a non-empty vector *)
Definition shiftout {A} := @rectS _ (fun n _ => t A n) (fun a => [])
  (fun h _ _ H => h :: H).
Global Arguments shiftout {A} {n} v.

(** Add an element at the end of a vector *)
Fixpoint shiftin {A} {n:nat} (a : A) (v:t A n) : t A (S n) :=
match v with
  |[] => a :: []
  |h :: t => h :: (shiftin a t)
end.

(** Copy last element of a vector *)
Definition shiftrepeat {A} := @rectS _ (fun n _ => t A (S (S n)))
  (fun h =>  h :: h :: []) (fun h _ _ H => h :: H).
Global Arguments shiftrepeat {A} {n} v.

(** Take first [p] elements of a vector *)
Fixpoint take {A} {n} (p:nat) (le:p <= n) (v:t A n) : t A p := 
  match p as p return p <= n -> t A p with 
  | 0 => fun _ => [] 
  | S p' => match v in t _ n return S p' <= n -> t A (S p') with
    | []=> fun le => False_rect _ (Nat.nle_succ_0 p' le)
    | x::xs => fun le => x::take p' (le_S_n p' _ le) xs
    end 
  end le.

(** Remove [p] last elements of a vector *)
Lemma trunc : forall {A} {n} (p:nat), n > p -> t A n
  -> t A (n - p).
Proof.
  induction p as [| p f]; intros H v.
  rewrite <- minus_n_O.
  exact v.

  apply shiftout.

  rewrite minus_Sn_m.
  apply f.
  auto with *.
  exact v.
  auto with *.
Defined.

(** Concatenation of two vectors *)
Fixpoint append {A}{n}{p} (v:t A n) (w:t A p):t A (n+p) :=
  match v with
  | [] => w
  | a :: v' => a :: (append v' w)
  end.

Infix "++" := append.

(** Two definitions of the tail recursive function that appends two lists but
reverses the first one *)

(** This one has the exact expected computational behavior *)
Fixpoint rev_append_tail {A n p} (v : t A n) (w: t A p)
  : t A (tail_plus n p) :=
  match v with
  | [] => w
  | a :: v' => rev_append_tail v' (a :: w)
  end.

Import EqdepFacts.

(** This one has a better type *)
Definition rev_append {A n p} (v: t A n) (w: t A p)
  :t A (n + p) :=
  rew <- (plus_tail_plus n p) in (rev_append_tail v w).

(** rev [a₁ ; a₂ ; .. ; an] is [an ; a{n-1} ; .. ; a₁]

Caution : There is a lot of rewrite garbage in this definition *)
Definition rev {A n} (v : t A n) : t A n :=
 rew <- (plus_n_O _) in (rev_append v []).

End BASES.
Local Notation "v [@ p ]" := (nth v p) (at level 1).

Section ITERATORS.
(** * Here are special non dependent useful instantiation of induction
schemes *)

(** Uniform application on the arguments of the vector *)
Definition map {A} {B} (f : A -> B) : forall {n} (v:t A n), t B n :=
  fix map_fix {n} (v : t A n) : t B n := match v with
  | [] => []
  | a :: v' => (f a) :: (map_fix v')
  end.

(** map2 g [x1 .. xn] [y1 .. yn] = [(g x1 y1) .. (g xn yn)] *)
Definition map2 {A B C} (g:A -> B -> C) :
  forall (n : nat), t A n -> t B n -> t C n :=
@rect2 _ _ (fun n _ _ => t C n) (nil C) (fun _ _ _ H a b => (g a b) :: H).
Global Arguments map2 {A B C} g {n} v1 v2.

(** fold_left f b [x1 .. xn] = f .. (f (f b x1) x2) .. xn *)
Definition fold_left {A B:Type} (f:B->A->B): forall (b:B) {n} (v:t A n), B :=
  fix fold_left_fix (b:B) {n} (v : t A n) : B := match v with
    | [] => b
    | a :: w => (fold_left_fix (f b a) w)
  end.

(** fold_right f [x1 .. xn] b = f x1 (f x2 .. (f xn b) .. ) *)
Definition fold_right {A B : Type} (f : A->B->B) :=
  fix fold_right_fix {n} (v : t A n) (b:B)
  {struct v} : B :=
  match v with
    | [] => b
    | a :: w => f a (fold_right_fix w b)
  end.

(** fold_right2 g c [x1 .. xn] [y1 .. yn] = g x1 y1 (g x2 y2 .. (g xn yn c) .. )
    c is before the vectors to be compliant with "refolding". *)
Definition fold_right2 {A B C} (g:A -> B -> C -> C) (c: C) :=
@rect2 _ _ (fun _ _ _ => C) c (fun _ _ _ H a b => g a b H).


(** fold_left2 f b [x1 .. xn] [y1 .. yn] = g .. (g (g a x1 y1) x2 y2) .. xn yn *)
Definition fold_left2 {A B C: Type} (f : A -> B -> C -> A) :=
fix fold_left2_fix (a : A) {n} (v : t B n) : t C n -> A :=
match v in t _ n0 return t C n0 -> A with
  |[] => fun w => case0 (fun _ => A) a w
  |@cons _ vh vn vt => fun w =>
    caseS' w (fun _ => A) (fun wh wt => fold_left2_fix (f a vh wh) vt wt)
end.

End ITERATORS.

Section SCANNING.
Inductive Forall {A} (P: A -> Prop): forall {n} (v: t A n), Prop :=
 |Forall_nil: Forall P []
 |Forall_cons {n} x (v: t A n): P x -> Forall P v -> Forall P (x::v).
Hint Constructors Forall.

Inductive Exists {A} (P:A->Prop): forall {n}, t A n -> Prop :=
 |Exists_cons_hd {m} x (v: t A m): P x -> Exists P (x::v)
 |Exists_cons_tl {m} x (v: t A m): Exists P v -> Exists P (x::v).
Hint Constructors Exists.

Inductive In {A} (a:A): forall {n}, t A n -> Prop :=
 |In_cons_hd {m} (v: t A m): In a (a::v)
 |In_cons_tl {m} x (v: t A m): In a v -> In a (x::v).
Hint Constructors In.

Inductive Forall2 {A B} (P:A->B->Prop): forall {n}, t A n -> t B n -> Prop :=
 |Forall2_nil: Forall2 P [] []
 |Forall2_cons {m} x1 x2 (v1:t A m) v2: P x1 x2 -> Forall2 P v1 v2 ->
    Forall2 P (x1::v1) (x2::v2).
Hint Constructors Forall2.

Inductive Exists2 {A B} (P:A->B->Prop): forall {n}, t A n -> t B n -> Prop :=
 |Exists2_cons_hd {m} x1 x2 (v1: t A m) (v2: t B m): P x1 x2 -> Exists2 P (x1::v1) (x2::v2)
 |Exists2_cons_tl {m} x1 x2 (v1:t A m) v2: Exists2 P v1 v2 -> Exists2 P (x1::v1) (x2::v2).
Hint Constructors Exists2.

End SCANNING.

Section VECTORLIST.
(** * vector <=> list functions *)

Fixpoint of_list {A} (l : list A) : t A (length l) :=
match l as l' return t A (length l') with
  |Datatypes.nil => []
  |(h :: tail)%list => (h :: (of_list tail))
end.

Definition to_list {A}{n} (v : t A n) : list A :=
Eval cbv delta beta in fold_right (fun h H => Datatypes.cons h H) v Datatypes.nil.
End VECTORLIST.

Module VectorNotations.
Delimit Scope vector_scope with vector.
Notation "[ ]" := [] (format "[ ]") : vector_scope.
Notation "h :: t" := (h :: t) (at level 60, right associativity)
  : vector_scope.
Notation "[ x ]" := (x :: []) : vector_scope.
Notation "[ x ; y ; .. ; z ]" := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..)) : vector_scope.
Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : vector_scope.
Infix "++" := append : vector_scope.
Open Scope vector_scope.
End VectorNotations.
