Require Program.Tactics.

(* To anticipate that obligations may declare universes, we require
   extensibility of the universe declaration for Program defintiions *)
Fail Program Definition foo@{u} : Type@{u} := _.

(* Similar tests *)

Fail Program Fixpoint foo@{u} (n:nat) : Type@{u} := _.

Fail Program Fixpoint foo@{u} (n:nat) {measure n} : Type@{u} := _.
