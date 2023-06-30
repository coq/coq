

#[universes(template=no)]
Record R := r { x : True }.
Check R : Prop.

Inductive I := i (_:True).
Check I : Prop.

Class Foo := foo : True.
Check Foo : Prop.

Class Thing := thing : True -> nat.
Check Thing : Set.
Fail Check Thing : Prop.

Axiom sTrue : SProp.

Class sFoo := sfoo : sTrue.

Axiom T : Type.

Class CT := ct : T.
