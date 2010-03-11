(* Some tests of the SearchPattern command *)

(* Simple, random tests *)
SearchPattern bool.
SearchPattern nat.
SearchPattern le.

(* With some hypothesis *)
SearchPattern (nat -> nat).
SearchPattern (?n * ?m + ?n = ?n * S ?m).

(* Non-linearity *)
SearchPattern (_ ?X ?X).

(* Non-linearity with hypothesis *)
SearchPattern (forall (x:?A) (y:?B), _ ?A ?B).

(* No delta-reduction *)
SearchPattern (Exc _).
