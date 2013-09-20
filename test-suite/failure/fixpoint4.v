(* Check that arguments of impredicative types are not considered
   subterms even through commutative cuts on functional arguments
   (example prepared by Bruno) *)

Inductive IMP : Prop :=
  CIMP : (forall A:Prop, A->A) -> IMP
| LIMP : (nat->IMP)->IMP.

Definition i0 := (LIMP (fun _ => CIMP (fun _ x => x))).

Fail Definition Paradox : False :=
 (fix F y o {struct o} : False :=
  match y with
  | tt => fun f =>
     match f 0 with
     | CIMP h => F y (h _ o)
     | _ => F y (f 0)
     end
  end match o with LIMP f => f | _ => fun _ => o end) tt i0.
