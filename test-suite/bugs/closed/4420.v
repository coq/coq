Module foo.
  Context (Char : Type).
  Axiom foo : Type -> Type.
  Goal foo Char = foo Char.
    change foo with (fun x => foo x).
    cbv beta.
    reflexivity.
  Defined. 
End foo.

Inductive foo (A : Type) : Prop := I. (*Top.1*)
Lemma bar : foo Type. (*Top.3*)
Proof.
  Set Printing Universes.
change foo with (fun x : Type => foo x). (*Top.4*)
cbv beta.
apply I. (* I Type@{Top.3} : (fun x : Type@{Top.4} => foo x) Type@{Top.3} *)
Defined.

