(**** Tactics Tauto and Intuition ****)

(**** Tauto:
  Tactic for automating proof in Intuionnistic Propositional Calculus, based on
  the contraction-free LJT of Dickhoff ****)

(**** Intuition:
  Simplifications of goals, based on LJT calcul ****)

(**** Introduction heuristic w.r.t. the dependent products:
 - Initially: Intros until the first non-dependent product and Intros of all
   the non-dependent products
 - In the algorithm: Intros only the non-dependent products ****)

(* Fails because False is after a dependent product which is after a
   non-dependent product *)
Goal (x,y:nat)x=y->(z:nat)False->x=z.
Proof.
  Tauto.
