(* Check that arguments of impredicative types are not considered
   subterms for the guard condition (an example by Thierry Coquand) *)

Inductive I : Prop :=
| C: (forall P:Prop, P->P) -> I.

Definition i0 := C (fun _ x => x).

Fail Definition Paradox : False :=
 (fix ni i : False :=
  match i with
  | C f => ni (f _ i)
  end) i0.
