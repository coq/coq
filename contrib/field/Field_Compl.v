(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Inductive listT (A:Type) : Type :=
  | nilT : listT A
  | consT : A -> listT A -> listT A.

Fixpoint appT (A:Type) (l m:listT A) {struct l} : listT A :=
  match l with
  | nilT => m
  | consT a l1 => consT A a (appT A l1 m)
  end.

Inductive prodT (A B:Type) : Type :=
    pairT : A -> B -> prodT A B.

Definition assoc_2nd :=
  (fix assoc_2nd_rec (A:Type) (B:Set)
                     (eq_dec:forall e1 e2:B, {e1 = e2} + {e1 <> e2})
                     (lst:listT (prodT A B)) {struct lst} : 
   B -> A -> A :=
     fun (key:B) (default:A) =>
       match lst with
       | nilT => default
       | consT (pairT v e) l =>
           match eq_dec e key with
           | left _ => v
           | right _ => assoc_2nd_rec A B eq_dec l key default
           end
       end).

Definition fstT (A B:Type) (c:prodT A B) := match c with
                                            | pairT a _ => a
                                            end.

Definition sndT (A B:Type) (c:prodT A B) := match c with
                                            | pairT _ a => a
                                            end.

Definition mem :=
  (fix mem (A:Set) (eq_dec:forall e1 e2:A, {e1 = e2} + {e1 <> e2}) 
           (a:A) (l:listT A) {struct l} : bool :=
     match l with
     | nilT => false
     | consT a1 l1 =>
         match eq_dec a a1 with
         | left _ => true
         | right _ => mem A eq_dec a l1
         end
     end).

Inductive field_rel_option (A:Type) : Type :=
  | Field_None : field_rel_option A
  | Field_Some : (A -> A -> A) -> field_rel_option A.