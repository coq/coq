(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Require Import List.

Definition assoc_2nd :=
  (fix assoc_2nd_rec (A:Type) (B:Set)
                     (eq_dec:forall e1 e2:B, {e1 = e2} + {e1 <> e2})
                     (lst:list (prod A B)) {struct lst} :
   B -> A -> A :=
     fun (key:B) (default:A) =>
       match lst with
       | nil => default
       | (v,e) :: l =>
           match eq_dec e key with
           | left _ => v
           | right _ => assoc_2nd_rec A B eq_dec l key default
           end
       end).

Definition mem :=
  (fix mem (A:Set) (eq_dec:forall e1 e2:A, {e1 = e2} + {e1 <> e2})
           (a:A) (l:list A) {struct l} : bool :=
     match l with
     | nil => false
     | a1 :: l1 =>
         match eq_dec a a1 with
         | left _ => true
         | right _ => mem A eq_dec a l1
         end
     end).
