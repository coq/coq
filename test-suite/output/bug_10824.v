Module A.
Notation F := False.
Notation "!!" := False (at level 100).
Check False.
End A.

Module B.
Notation "!!" := False (at level 100).
Notation F := False.
Notation "!!" := False (at level 100).
Check False.
End B.
