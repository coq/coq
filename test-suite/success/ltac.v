(* The tactic language *)

(* Submitted by Pierre Crégut *)
(* Checks substitution of x *)
Tactic Definition f x := Unfold x; Idtac.
 
Goal (plus O O) = O.
f plus.
