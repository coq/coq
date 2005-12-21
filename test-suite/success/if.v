(* The synthesis of the elimination predicate may fail if algebric *)
(* universes are not cautiously treated *)

Check (fun b : bool => if b then Type else nat).

