
(* Refine and let-in's *)

Goal (EX x:nat | x=O).
Refine let y = (plus O O) in ?.
Exists y; Auto.
Save test1.

Goal (EX x:nat | x=O).
Refine let y = (plus O O) in (ex_intro ? ? (plus y y) ?).  
Auto.
Save test2.

Goal nat.
Refine let y = O in (plus O ?).
Exact (S O).
Save test3.

(* Example submitted by Yves on coqdev *)

Require PolyList.

Goal (l:(list nat))l=l.
Proof.
Refine [l]<[l]l=l>
       Cases l of
       | nil => ?
       | (cons O l0) => ?
       | (cons (S _) l0) => ?
       end.
Abort.

(* Submitted by Roland Zumkeller (bug #888) *)

(* The Fix and CoFix rules expect a subgoal even for closed components of the
   (co-)fixpoint *)

Goal nat -> nat.
Refine(
  Fix f {f [n:nat] : nat := (S ?) with
         pred [n:nat] : nat := n}).
Intro; Exact 0.
Qed.

(* Submitted by Roland Zumkeller (bug #889) *)

(* The types of metas were in metamap and they were not updated when
   passing through a binder *)

Goal (n:nat) nat -> n=0.
Refine [n]
  Fix f { f [i:nat] : n=0 :=
    Cases i of 0 => ? | (S _) => ? end }.
Abort.

