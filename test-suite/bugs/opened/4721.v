Variables S1 S2 : Set.

Goal @eq Type S1 S2 -> @eq Type S1 S2.
intro H.
Fail tauto.
assumption.
Qed.

(*This is in 8.5pl1, and Matthieq Sozeau says: "That's a regression in tauto indeed, which now requires exact equality of the universes, through a non linear goal pattern matching:
match goal with ?X1 |- ?X1 forces both instances of X1 to be convertible,
with no additional universe constraints currently, but the two types are
initially different. This can be fixed easily to allow the same flexibility
as in 8.4 (or assumption) to unify the universes as well."*)
