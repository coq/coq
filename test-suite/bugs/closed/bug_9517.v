Declare Custom Entry expr.
Declare Custom Entry stmt.
Notation "x" := x (in custom stmt, x ident).
Notation "x" := x (in custom expr, x ident).

Notation "1" := 1 (in custom expr).

Notation "! x = y !" := (pair x y) (in custom stmt at level 0, x custom expr, y custom expr).
Notation "? x = y" := (pair x y) (in custom stmt at level 0, x custom expr, y custom expr).
Notation "x = y" := (pair x y) (in custom stmt at level 0, x custom expr, y custom expr).

Notation "stmt:( s )" := s (s custom stmt).
Check stmt:(! _ = _ !).
Check stmt:(? _ = _).
Check stmt:(_ = _).
Check stmt:(! 1 = 1 !).
Check stmt:(? 1 = 1).
Check stmt:(1 = 1).
Check stmt:(_ = 1).
