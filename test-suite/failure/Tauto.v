(**** Tactics Tauto and Intuition ****)

(**** Tauto:
  Tactic for automating proof in Intuionnistic Propositional Calculus, based on
  the contraction-free LJT of Dickhoff ****)

(**** Intuition:
  Simplifications of goals, based on LJT calcul ****)

(* Fails because Tauto does not perform any Apply *)
Goal ((A:Prop)A\/~A)->(x,y:nat)(x=y\/~x=y).
Proof.
  Tauto.
