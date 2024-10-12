(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*          Pierre Letouzey, Jerome Vouillon, PPS, Paris 7, 2008        *)
(************************************************************************)

Local Set Warnings "-deprecated".

Local Open Scope type_scope.

Require Import List.

(** * Generic dependently-typed operators about [n]-ary functions *)

(** The type of [n]-ary function: [nfun A n B] is
    [A -> ... -> A -> B] with [n] occurrences of [A] in this type. *)

#[deprecated(since="8.19", note="Please step up to maintain NaryFunctions.v if you need it.")]
Fixpoint nfun A n B :=
  match n with
  | O => B
  | S n => A -> (nfun A n B)
  end.

#[deprecated(since="8.19", note="Please step up to maintain NaryFunctions.v if you need it.")]
Notation " A ^^ n --> B " := (nfun A n B)
  (at level 50, n at next level) : type_scope.

(** [napply_cst _ _ a n f] iterates [n] times the application of a
    particular constant [a] to the [n]-ary function [f]. *)

#[deprecated(since="8.19", note="Please step up to maintain NaryFunctions.v if you need it.")]
Fixpoint napply_cst (A B:Type)(a:A) n : (A^^n-->B) -> B :=
  match n return (A^^n-->B) -> B with
  | O => fun x => x
  | S n => fun x => napply_cst _ _ a n (x a)
  end.


(** A generic transformation from an n-ary function to another one.*)

#[deprecated(since="8.19", note="Please step up to maintain NaryFunctions.v if you need it.")]
Fixpoint nfun_to_nfun (A B C:Type)(f:B -> C) n :
  (A^^n-->B) -> (A^^n-->C) :=
  match n return (A^^n-->B) -> (A^^n-->C) with
  | O => f
  | S n => fun g a => nfun_to_nfun _ _ _ f n (g a)
  end.

(** [napply_except_last _ _ n f] expects [S n] arguments of type [A],
    applies [n] of them to [f] and discards the last one. *)

#[deprecated(since="8.19", note="Please step up to maintain NaryFunctions.v if you need it.")]
Fixpoint napply_except_last (A B:Type) (n : nat) (f : A^^n-->B) {struct n} : A^^S n-->B.
Proof.
  destruct n.
  - exact (fun _ => f).
  - exact (fun arg => napply_except_last A B n (f arg)).
Defined.

(** [napply_then_last _ _ a n f] expects [n] arguments of type [A],
    applies them to [f] and then apply [a] to the result. *)

#[deprecated(since="8.19", note="Please step up to maintain NaryFunctions.v if you need it.")]
Definition napply_then_last (A B:Type)(a:A) :=
  nfun_to_nfun A (A->B) B (fun fab => fab a).

(** [napply_discard _ b n] expects [n] arguments, discards then,
    and returns [b]. *)

#[deprecated(since="8.19", note="Please step up to maintain NaryFunctions.v if you need it.")]
Fixpoint napply_discard (A B:Type)(b:B) n : A^^n-->B :=
  match n return A^^n-->B with
  | O => b
  | S n => fun _ => napply_discard _ _ b n
  end.

(** A fold function *)

#[deprecated(since="8.19", note="Please step up to maintain NaryFunctions.v if you need it.")]
Fixpoint nfold A B (f:A->B->B)(b:B) n : (A^^n-->B) :=
  match n return (A^^n-->B) with
  | O => b
  | S n => fun a => (nfold _ _ f (f a b) n)
  end.


(** [n]-ary products : [nprod A n] is [A*...*A*unit],
  with [n] occurrences of [A] in this type. *)

#[deprecated(since="8.19", note="Please step up to maintain NaryFunctions.v if you need it.")]
Fixpoint nprod A n : Type := match n with
  | O => unit
  | S n => (A * nprod A n)%type
  end.

#[deprecated(since="8.19", note="Please step up to maintain NaryFunctions.v if you need it.")]
Notation "A ^ n" := (nprod A n) : type_scope.

(** [n]-ary curryfication / uncurryfication *)

#[deprecated(since="8.19", note="Please step up to maintain NaryFunctions.v if you need it.")]
Fixpoint ncurry (A B:Type) n : (A^n -> B) -> (A^^n-->B) :=
  match n return (A^n -> B) -> (A^^n-->B) with
  | O => fun x => x tt
  | S n => fun f a => ncurry _ _ n (fun p => f (a,p))
  end.

#[deprecated(since="8.19", note="Please step up to maintain NaryFunctions.v if you need it.")]
Fixpoint nuncurry (A B:Type) n : (A^^n-->B) -> (A^n -> B) :=
  match n return (A^^n-->B) -> (A^n -> B) with
  | O => fun x _ => x
  | S n => fun f p => let (x,p) := p in nuncurry _ _ n (f x) p
  end.

(** Earlier functions can also be defined via [ncurry/nuncurry].
    For instance : *)

#[deprecated(since="8.19", note="Please step up to maintain NaryFunctions.v if you need it.")]
Definition nfun_to_nfun_bis A B C (f:B->C) n :
  (A^^n-->B) -> (A^^n-->C) :=
  fun anb => ncurry _ _ n (fun an => f ((nuncurry _ _ n anb) an)).

(** We can also us it to obtain another [fold] function,
    equivalent to the previous one, but with a nicer expansion
    (see for instance Int31.iszero). *)

#[deprecated(since="8.19", note="Please step up to maintain NaryFunctions.v if you need it.")]
Fixpoint nfold_bis A B (f:A->B->B)(b:B) n : (A^^n-->B) :=
  match n return (A^^n-->B) with
  | O => b
  | S n => fun a =>
      nfun_to_nfun_bis _ _ _ (f a) n (nfold_bis _ _ f b n)
  end.

(** From [nprod] to [list] *)

#[deprecated(since="8.19", note="Please step up to maintain NaryFunctions.v if you need it.")]
Fixpoint nprod_to_list (A:Type) n : A^n -> list A :=
  match n with
  | O => fun _ => nil
  | S n => fun p => let (x,p) := p in x::(nprod_to_list _ n p)
  end.

(** From [list] to [nprod] *)

#[deprecated(since="8.19", note="Please step up to maintain NaryFunctions.v if you need it.")]
Fixpoint nprod_of_list (A:Type)(l:list A) : A^(length l) :=
  match l return A^(length l) with
  | nil => tt
  | x::l => (x, nprod_of_list _ l)
  end.

(** This gives an additional way to write the fold *)

#[deprecated(since="8.19", note="Please step up to maintain NaryFunctions.v if you need it.")]
Definition nfold_list (A B:Type)(f:A->B->B)(b:B) n : (A^^n-->B) :=
  ncurry _ _ n (fun p => fold_right f b (nprod_to_list _ _ p)).
