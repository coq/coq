Declare Scope blafu.
Delimit Scope blafu with B.
Axiom DoesNotMatch : Type.
Axiom consumer : forall {A} (B : A -> Type) (E:Type) (x : A) (ls : list nat), unit.

Notation "|  p1  |  ..  |  pn" := (@cons _ p1 .. (@cons _ pn nil) ..) (at level 91) : blafu.
Notation "'mmatch_do_not_write' x 'in' T 'as' y 'return' 'M' p 'with_do_not_write' ls" :=
    (@consumer _ (fun y : T => p%type) DoesNotMatch x ls%B)
      (at level 200, ls at level 91, only parsing).
Notation "'mmatch' x 'in' T 'as' y 'return' 'M' p 'with' ls 'end'" :=
  (mmatch_do_not_write x in T as y return M p with_do_not_write ls)
    (at level 200, ls at level 91, p at level 10, only parsing).
(* This should not gives a warning *)
Notation "'mmatch' x 'in' T 'as' y 'return' 'M' p 'with' ls 'end'" :=
  (@consumer _ (fun y : T => p%type) DoesNotMatch x ls%B)
    (at level 200, ls at level 91, p at level 10, only printing,
     format "'[  ' mmatch  '/' x ']'  '/' '[  ' in  '/' T ']'  '/' '[  ' as  '/' y ']'  '/' '[  ' return  M  p ']'  with  '//' '[' ls ']'  '//' end"
     ).
