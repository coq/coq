(* File reduced by coq-bug-finder from original input, then from 1829 lines to 37 lines, then from 47 lines to 18 lines *)

Class Contr_internal (A : Type) :=
  BuildContr { center : A ;
               contr : (forall y : A, True) }.
Class Contr A := Contr_is_contr : Contr_internal A.
Inductive Unit : Set := tt.
Instance contr_unit : Contr Unit | 0 :=
  let x := {|
        center := tt;
        contr := fun t : Unit => I
      |} in x. (* success *)

Instance contr_internal_unit' : Contr_internal Unit | 0 :=
  {|
    center := tt;
    contr := fun t : Unit => I
  |}.

Instance contr_unit' : Contr Unit | 0 :=
  {|
    center := tt;
    contr := fun t : Unit => I
  |}.
(* Error: Mismatched contexts while declaring instance:
 Expected: (Contr_is_contr : Contr_internal _UNBOUND_REL_1)
 Found:   tt  (fun t : Unit => I) *)
