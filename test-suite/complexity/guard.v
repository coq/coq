(* Examples to check that the guard condition does not unfold
   irrelevant subterms *)
(* Expected time < 1.00s *)
Require Import Bool.

Fixpoint slow n :=
 match n with
 | 0 => true
 | S k => andb (slow k) (slow k)
 end.

Timeout 5 Time Fixpoint F n :=
  match n with
  | 0 => 0
  | S k =>
    if slow 100 then F k else 0
  end.
