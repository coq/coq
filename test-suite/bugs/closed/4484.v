(* Testing 8.5 regression with type classes not solving evars 
   redefined while trying to solve them with the type class mechanism *)

Class A := {}.
Axiom foo : forall {ac : A}, bool.
Lemma bar (ac : A) : True.
Check (match foo as k return foo = k -> True with
       | true => _
       | false => _
       end eq_refl).
