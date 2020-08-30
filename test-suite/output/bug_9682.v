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
(* Check use of "mmatch" *)
Check (mmatch 1 + 2 + 3 + 4 + 5 + 6 in nat as x return M (x = x) with | 1 end).

(* 2nd example *)
Notation "#" := I (at level 0, only parsing).
Notation "#" := I (at level 0, only printing).
Check #.
Notation "##" := I (at level 0, only printing).
Notation "##" := I (at level 0, only parsing).
Check ##.
