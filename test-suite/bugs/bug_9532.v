Declare Custom Entry atom.
Notation "1" := tt (in custom atom).
Notation "atom:( s )" := s (s custom atom).

Declare Custom Entry expr.
Notation "expr:( s )" := s (s custom expr).
Notation "( x , y , .. , z )" :=  (@cons unit x (@cons unit y .. (@cons unit z (@nil unit)) ..))
  (in custom expr at level 0, x custom atom, y custom atom, z custom atom).

Check atom:(1).
Check expr:((1,1)).
Check expr:((1,1,1)).
