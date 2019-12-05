CoInductive stream :=
| C : content -> stream
with content :=
| D : nat -> stream -> content.

Lemma one : stream.
cofix c with (d : content).
- constructor. apply d.
- constructor. exact 1. apply c.
Defined.
