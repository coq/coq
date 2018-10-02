Class Equiv A := equiv: A -> A -> Prop.
Infix "=" := equiv : type_scope.

Class Associative {A} f `{Equiv A} := associativity x y z : f x (f y z) = f (f x y) z.

Class SemiGroup A op `{Equiv A} := { sg_ass :>> Associative op }.

Class SemiLattice A op `{Equiv A} :=
    { semilattice_sg :>> SemiGroup A op
    ; redundant : Associative op
    }.
