(* Slightly improving interpretation of Ltac subterms in notations *)

Notation "'var2' x .. y = z ; e" := (ltac:(exact z), (fun x => .. (fun y => e)
..)) (at level 200, x binder, y binder, e at level 220).
Check (var2 a = 1; a).
