
(* Refine and let-in's *)

Goal exists x : nat, x = 0.
 refine (let y := 0 + 0 in _).
exists y; auto.
Save test1.

Goal exists x : nat, x = 0.
 refine (let y := 0 + 0 in ex_intro _ (y + y) _).  
auto.
Save test2.

Goal nat.
 refine (let y := 0 in 0 + _).
exact 1.
Save test3.

(* Example submitted by Yves on coqdev *)

Require Import List.

Goal forall l : list nat, l = l.
Proof.
 refine
 (fun l =>
  match l return (l = l) with
  | nil => _
  | O :: l0 => _
  | S _ :: l0 => _
  end).
Abort.

(* Submitted by Roland Zumkeller (bug #888) *)

(* The Fix and CoFix rules expect a subgoal even for closed components of the
   (co-)fixpoint *)

Goal nat -> nat.
 refine (fix f (n : nat) : nat := S _
         with pred (n : nat) : nat := n
         for f).
exact 0.
Qed.

(* Submitted by Roland Zumkeller (bug #889) *)

(* The types of metas were in metamap and they were not updated when
   passing through a binder *)

Goal forall n : nat, nat -> n = 0.
 refine
 (fun n => fix f (i : nat) : n = 0 := match i with
                                      | O => _
                                      | S _ => _
                                      end).
Abort.

(* Submitted by Roland Zumkeller (bug #931) *)
(* Don't turn dependent evar into metas *)

Goal (forall n : nat, n = 0 -> Prop) -> Prop.
intro P.
 refine (P _ _).
reflexivity.
Abort.
