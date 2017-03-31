Set Universe Polymorphism.

Definition foo@{i j} (A : Type@{i}) (B : Type@{j}) := A.

Set Printing Universes.

Fail Definition bar@{i} (A : Type@{i}) (B : Type) := A.

Definition baz@{i j} (A : Type@{i}) (B : Type@{j}) := (A * B)%type.

Fail Definition bad@{i j} (A : Type@{i}) (B : Type@{j}) : Type := (A * B)%type.

Fail Definition bad@{i} (A : Type@{i}) (B : Type@{j}) : Type := (A * B)%type.

Definition shuffle@{i j} (A : Type@{j}) (B : Type@{i}) := (A * B)%type.

Definition nothing (A : Type) := A.

Inductive bla@{l k} : Type@{k} := blaI : Type@{l} -> bla.

Inductive blacopy@{k l} : Type@{k} := blacopyI : Type@{l} -> blacopy.


Class Wrap A := wrap : A.

Fail Instance bad@{} : Wrap Type := Type.

Instance bad@{} : Wrap Type.
Fail Proof Type.
Abort.

Instance bar@{u} : Wrap@{u} Set. Proof nat.


Monomorphic Universe g.

Inductive blacopy'@{l} : Type@{g} := blacopy'I : Type@{l} -> blacopy'.
