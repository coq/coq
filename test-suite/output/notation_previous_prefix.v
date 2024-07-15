Reserved Notation "#0 x" (at level 30).
Reserved Notation "#0 #1 x".
Print Notation "#0 #1 _".

Declare Custom Entry foo.
Reserved Notation "#0 x" (in custom foo at level 40).
Reserved Notation "#0 #1 x" (in custom foo).
Print Notation "#0 #1 _" in custom foo.

Reserved Notation "#2 x #3 y" (at level 30, x at level 20, y at level 25).
Reserved Notation "#2 z #3 x #4 y".
Print Notation "#2 _ #3 _ #4 _".
