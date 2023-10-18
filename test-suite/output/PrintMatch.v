(* NB feel free to add other tests about printing match, not just about Match All Subterms *)

Module MatchAllSubterms.

Set Printing Match All Subterms.
Set Printing Universes.

Polymorphic Inductive eqT@{u} {A:Type@{u}} (a:A) : A -> Type@{u} := reflT : eqT a a.
Print eqT_rect.

Set Definitional UIP.
Inductive seq {A} (a:A) : A -> SProp := srefl : seq a a.
Print seq_rect.

End MatchAllSubterms.

Module Bug18163.

Set Printing All.
Print eq_sym.
Unset Printing All.

Set Printing Implicit.
Print eq_sym.

Set Asymmetric Patterns.
Print eq_sym.

End Bug18163.
