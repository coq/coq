Set Primitive Projections.
Set Universe Polymorphism.
Record ptd := Ptd { t : Type ; p : t }.
Definition type := Ptd Type (unit:Type).
Definition type' := Ptd Type (p type).
Canonical type'.
