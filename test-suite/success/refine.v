
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
