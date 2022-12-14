(* NB feel free to add other tests about printing match, not just about Match All Subterms *)

Set Printing Match All Subterms.
Set Printing Universes.

Polymorphic Inductive eqT@{u} {A:Type@{u}} (a:A) : A -> Type@{u} := reflT : eqT a a.
Print eqT_rect.

Set Definitional UIP.
Inductive seq {A} (a:A) : A -> SProp := srefl : seq a a.
Print seq_rect.
