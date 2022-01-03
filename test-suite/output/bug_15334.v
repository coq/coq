Declare Custom Entry ent.
Notation "ent:( x )" := x (x custom ent).
Notation "a ; b" := (pair a b) (in custom ent at level 50).
Check ent:(_ ; _).
