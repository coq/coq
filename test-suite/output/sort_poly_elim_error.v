Set Universe Polymorphism.
Inductive sum@{s|u v|} (A : Type@{s|u}) (B : Type@{s|v}) : Type@{s|max(u,v)} :=
  | inl : A -> sum A B
  | inr : B -> sum A B.
Arguments inl {A B}.
Arguments inr {A B}.

Fail Check (fun p : sum@{Prop|_ _} True False => match p return Set with inl a => unit | inr b => bool end).
(*
Error: Incorrect elimination of "p" in the inductive type "sum":
the return type has sort "Type@{Set+1}" while it should be at some variable quality.
Elimination of an inductive object of sort Type is not allowed on a predicate in sort Type
because wrong arity.
*)


Inductive sBox@{s s'|u|} (A:Type@{s|u}) : Type@{s'|u} := sbox (_:A).

Fail Definition elim@{s s'|u|} (A:Type@{s|u}) (x:sBox@{s s'|u} A) : A :=
  match x with sbox _ v => v end.

Inductive sP : SProp := sC.

Fail Check match sC with sC => I end.
