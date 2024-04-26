
Set Universe Polymorphism.
Set Printing Universes.

(* Fully explicit definition: we would like to spare the annotation u *)
Definition id@{s|u|} (A : Type@{s|u}) (a : A) : A := a.


(* Some kind of typical ambiguity can be simulated by rebinding Type to an auxilliary definition T*)
Definition T@{s|u|} := Type@{s|u}.
Definition idT@{s|+|} (A : T@{s|_}) (a : A) : A := a.

(* The actual problem *)
Definition id0@{s|+|} (A : Type@{s|_}) (a : A) : A := a.
(*
Error:
Syntax error: [universe] expected after '|' (in [sort]).
 *)

(* check that we didn't forget the quality annotation *)
Check fun (A:SProp) (x:A) => id0 A x.
