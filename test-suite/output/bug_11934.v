Cumulative Polymorphic Axiom foo@{u} : Prop -> Prop.
Arguments foo {_}.

Axiom bla : forall {A B}, @foo A -> @foo B -> Prop.
Definition thing := forall (x:@foo@{Type} True) (y:@foo@{Type} True), bla x y.

Print thing. (* forall x y : foo, bla x y *)

Set Printing Universes.
Print thing. (* forall (x : foo@{thing.u0}) (y : foo@{thing.u1}), bla x y *)

Set Printing Implicit.
Print thing. (* BAD: forall x y : @foo@{thing.u0} True, @bla True True x y *)
