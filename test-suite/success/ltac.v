(* The tactic language *)

(* Submitted by Pierre Crégut *)
(* Checks substitution of x *)
Tactic Definition f x := Unfold x; Idtac.
 
Lemma lem1 : (plus O O) = O.
f plus.
Qed.

(* Check that Match Context keeps a closure *)
Tactic Definition U := Let a = 'I In Match Context With [ |- ? ] -> Apply a.

Lemma lem2 : True.
U.
Qed
