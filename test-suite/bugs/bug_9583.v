(* Was causing a stack overflow before #11613 *)
Declare Custom Entry bla.
Notation "[ t ]" := (t) (at level 0, t custom bla at level 0).
Notation "] t [" := (t) (in custom bla at level 0, t custom bla at level 0).
Notation "t" := (t) (in custom bla at level 0, t constr at level 9).
Notation "0" := (0) (in custom bla at level 0).
Check fun x => [ ] x [ ].
