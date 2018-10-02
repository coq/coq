Variables P Q : Prop.
Axiom pqrw : P <-> Q.

Require Setoid.

Goal P -> Q.
unshelve (rewrite pqrw).
