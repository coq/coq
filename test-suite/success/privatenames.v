
Set Warnings "+generated-names".

(* Check that refine policy of redefining previous names make these names private *)

Goal forall x y, x+y=0.
intro x.
refine (fun x => _).
Fail Check x0.
Check x.
Abort.

(* Example from Emilio *)

Goal forall b : False, b = b.
intro b.
refine (let b := I in _).
Fail destruct b0.
Abort.

(* Example from Cyprien *)

Goal True -> True.
Proof.
  refine (fun _ => _).
  Fail exact t.
Abort.
