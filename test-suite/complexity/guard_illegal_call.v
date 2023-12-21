(* Examples to check that the guard condition does not evaluate
   irrelevant subterms *)
(* Expected time < 1.00s *)

Fixpoint slow n (s:bool) :=
 match n with
 | 0 => true
 | S k => andb (slow k s) (slow k s)
 end.

Timeout 5 Time Fixpoint F s n :=
  match n with
  | 0 => fun _ => 0
  | S k => fun s' => F s k
  end (slow 100 s).
