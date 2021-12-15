(* Checking support for scope delimiters and as clauses in 'pat
   applied to notations with binders *)

Notation "'multifun' x .. y 'in' f" := (fun x => .. (fun y => f) .. )
  (at level 200, x binder, y binder, f at level 200).

Check multifun '((x, y)%core as z) in (x+y,0)=z.
