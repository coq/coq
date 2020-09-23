Undelimit Scope list_scope.
Declare Custom Entry gnat.
Declare Custom Entry gargs.

Notation "!" := 42 (in custom gnat).
Notation "gargs:( e  )" := e (e custom gargs).
Notation "( x )" := (cons x (@nil nat)) (in custom gargs, x custom gnat).
Notation "( x , y , .. , z )" := (cons x (cons y .. (cons z nil) ..))
  (in custom gargs, x custom gnat, y custom gnat, z custom gnat).

Check gargs:( (!) ). (* cons 42 nil *)
Check gargs:( (!, !, !) ). (* cons 42 (42 :: 42 :: nil) *)

Definition OnlyGargs {T} (x:T) := x.
Notation "OnlyGargs[ x  ]" := (OnlyGargs x) (at level 10, x custom gargs).
Check OnlyGargs[ (!) ]. (* OnlyGargs[ cons 42 nil] *)

Declare Custom Entry gargs999.
Notation "gargs999:( e  )" := e (e custom gargs999 at level 999).
Notation "( x )" := (cons x (@nil nat)) (in custom gargs999, x custom gnat at level 999).
Notation "( x , y , .. , z )" := (cons x (cons y .. (cons z nil) ..))
  (in custom gargs999, x custom gnat at level 999, y custom gnat at level 999, z custom gnat at level 999).

Check gargs999:( (!) ). (* gargs999:( (!)) *)
Check gargs999:( (!, !, !) ). (* gargs999:( (!, !, !)) *)
Check OnlyGargs[ (!) ]. (* OnlyGargs[ gargs999:( (!))] *)

Definition OnlyGargs999 {T} (x:T) := x.
Notation "OnlyGargs999[ x  ]" := (OnlyGargs999 x) (at level 10, x custom gargs999 at level 999).
Check OnlyGargs999[ (!) ]. (* OnlyGargs999[ (!)] *)
