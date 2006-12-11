(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import BinPos.
Require Import List.

Ltac list_fold_right fcons fnil l :=
  match l with
  | (cons ?x ?tl) => fcons x ltac:(list_fold_right fcons fnil tl)
  | nil => fnil
  end.

Ltac lazy_list_fold_right fcons fnil l :=
  match l with
  | (cons ?x ?tl) => 
       let cont := lazy_list_fold_right fcons fnil in
       fcons x cont tl
  | nil => fnil 
  end.

Ltac list_fold_left fcons fnil l :=
  match l with
  | (cons ?x ?tl) => list_fold_left fcons ltac:(fcons x fnil) tl
  | nil => fnil
  end.

Ltac list_iter f l :=
  match l with
  | (cons ?x ?tl) => f x; list_iter f tl
  | nil => idtac
  end.

Ltac list_iter_gen seq f l :=
  match l with
  | (cons ?x ?tl) =>
      let t1 _ := f x in
      let t2 _ := list_iter_gen seq f tl in
      seq t1 t2
  | nil => idtac
  end.

Ltac AddFvTail a l :=
 match l with
 | nil          => constr:(cons a l)
 | (cons a _)   => l
 | (cons ?x ?l) => let l' := AddFvTail a l in constr:(cons x l')
 end.

Ltac Find_at a l :=
 let rec find n l :=
   match l with
   | nil => fail 100 "anomaly: Find_at"
   | (cons a _) => eval compute in n
   | (cons _ ?l) => find (Psucc n) l
   end
 in find 1%positive l.

Ltac check_is_list t :=
  match t with
  | cons _ ?l => check_is_list l
  | nil => idtac
  | _ => fail 100 "anomaly: failed to build a canonical list"
  end.

Ltac check_fv l :=
  check_is_list l;
  match type of l with 
  | list _ => idtac
  | _ => fail 100 "anomaly: built an ill-typed list"
  end.
