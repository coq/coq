(* Declare empty levels in the same order they are computed *)

Notation "< a ; b ; c >1" :=
  (sum a (sum b c)) (at level 18, a at level 19, b at level 20, c at level 21).
Notation "< a ; b ; c >2" :=
  (sum a (sum b c)) (at level 28, a at level 29, c at level 32, b at level 31).
Notation "< a ; b ; c >3" :=
  (sum a (sum b c)) (at level 38, c at level 42, a at level 39, b at level 41).
Notation "< a ; b ; c >4" :=
  (sum a (sum b c)) (at level 48, c at level 52, b at level 51, a at level 49).
Notation "< a ; b >" :=
  (sum a b) (at level 61, a at level 63, b at level 62).
