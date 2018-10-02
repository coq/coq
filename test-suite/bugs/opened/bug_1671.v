(* Exemple soumis par Pierre Corbineau (bug #1671) *)

CoInductive hdlist : unit -> Type :=
| cons : hdlist tt -> hdlist tt.

Variable P : forall bo, hdlist bo -> Prop.
Variable all : forall bo l, P bo l.

Fail Definition F (l:hdlist tt) : P tt l :=
match l in hdlist u return P u l with
| cons (cons l') => all tt _
end.
