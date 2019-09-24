Set Allow StrictProp.
Unset Elaboration StrictProp Cumulativity.

Inductive Box (A:SProp) : Prop := box { unbox : A }.

Coercion Box : SProp >-> Sortclass.

Set Printing Coercions.
Check fun P : SProp => P : Set.
