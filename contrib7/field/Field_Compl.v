(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Inductive listT [A:Type] : Type :=
  nilT : (listT A) | consT : A->(listT A)->(listT A).

Fixpoint appT [A:Type][l:(listT A)] : (listT A) -> (listT A) :=
  [m:(listT A)]
  Cases l of
  | nilT => m 
  | (consT a l1) => (consT A a (appT A l1 m))
  end.

Inductive prodT [A,B:Type] : Type :=
  pairT: A->B->(prodT A B).

Definition assoc_2nd :=
Fix assoc_2nd_rec
  {assoc_2nd_rec 
   [A:Type;B:Set;eq_dec:(e1,e2:B){e1=e2}+{~e1=e2};lst:(listT (prodT A B))]
   : B->A->A:=
  [key:B;default:A]
  Cases lst of
  | nilT => default
  | (consT (pairT v e) l) =>
    (Cases (eq_dec e key) of
    | (left _) => v
    | (right _) => (assoc_2nd_rec A B eq_dec l key default)
    end)
  end}.

Definition fstT [A,B:Type;c:(prodT A B)] :=
  Cases c of
  | (pairT a _) => a
  end.

Definition sndT [A,B:Type;c:(prodT A B)] :=
  Cases c of
  | (pairT _ a) => a
  end.

Definition mem :=
Fix mem {mem [A:Set;eq_dec:(e1,e2:A){e1=e2}+{~e1=e2};a:A;l:(listT A)] : bool :=
  Cases l of
  | nilT => false
  | (consT a1 l1) =>
    Cases (eq_dec a a1) of
    | (left _) => true
    | (right _) => (mem A eq_dec a l1)
    end
  end}.

Inductive field_rel_option [A:Type] : Type :=
  | Field_None : (field_rel_option A)
  | Field_Some : (A -> A -> A) -> (field_rel_option A).
