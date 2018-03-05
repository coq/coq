(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import BinPos.
Require Import List.

Ltac list_fold_right fcons fnil l :=
  match l with
  | ?x :: ?tl => fcons x ltac:(list_fold_right fcons fnil tl)
  | nil => fnil
  end.

(* A variant of list_fold_right, to prevent the match of list_fold_right
   from catching errors raised by fcons. *)
Ltac lazy_list_fold_right fcons fnil l :=
  let f :=
    match l with
    | ?x :: ?tl =>
         fun _ =>
         fcons x ltac:(fun _ => lazy_list_fold_right fcons fnil tl)
    | nil => fun _ => fnil()
    end in
  f().

Ltac list_fold_left fcons fnil l :=
  match l with
  | ?x :: ?tl => list_fold_left fcons ltac:(fcons x fnil) tl
  | nil => fnil
  end.

Ltac list_iter f l :=
  match l with
  | ?x :: ?tl => f x; list_iter f tl
  | nil => idtac
  end.

Ltac list_iter_gen seq f l :=
  match l with
  | ?x :: ?tl =>
      let t1 _ := f x in
      let t2 _ := list_iter_gen seq f tl in
      seq t1 t2
  | nil => idtac
  end.

Ltac AddFvTail a l :=
 match l with
 | nil      => constr:(a::nil)
 | a :: _   => l
 | ?x :: ?l => let l' := AddFvTail a l in constr:(x::l')
 end.

Ltac Find_at a l :=
 let rec find n l :=
   match l with
   | nil     => fail 100 "anomaly: Find_at"
   | a :: _  => eval compute in n
   | _ :: ?l => find (Pos.succ n) l
   end
 in find 1%positive l.

Ltac check_is_list t :=
  match t with
  | _ :: ?l => check_is_list l
  | nil     => idtac
  | _       => fail 100 "anomaly: failed to build a canonical list"
  end.

Ltac check_fv l :=
  check_is_list l;
  match type of l with
  | list _ => idtac
  | _      => fail 100 "anomaly: built an ill-typed list"
  end.
