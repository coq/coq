Class Decodable (A : Type) := decode : nat -> option A.
Class ContainsType := { SomeType : Type; }.

Section ASection.
Context `{ContainsType}.

Inductive Wrap :=
  | wrap : SomeType -> Wrap.

Axiom any : forall {A}, A.
Global Instance inst : Decodable Wrap := any.
End ASection.

Instance impl : ContainsType :=
  {| SomeType := nat; |}.

(*
Error: Cannot infer the 1st argument of the inductive type (@Wrap) of this term (no type
class instance found) in environment:
n : nat
*)
Definition foo n :=
  match decode n with
  | Some (wrap _) => 0
  | _ => 0
  end.
