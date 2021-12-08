Definition id {T} (x : T) := x.
Goal sigT (fun x => id x)%type.
  change (fun x => ?f x) with f.
  exists Type. exact Set.
Defined. (* Error: Attempt to save a proof with shelved goals (in proof Unnamed_thm) *)
