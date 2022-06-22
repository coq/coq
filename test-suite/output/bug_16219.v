Inductive sUnit : SProp := stt.
Print Assumptions sUnit.
(* was bug: sUnit relies on definitional UIP. *)

Inductive squashed_eq {A} a : A -> SProp := squashed_refl : squashed_eq a a.
Print Assumptions squashed_eq.
Fail Check fun e : squashed_eq 0 1 => match e with squashed_refl _ => 2 end.

Set Definitional UIP.
Inductive seq {A} a : A -> SProp := srefl : seq a a.
Print Assumptions seq_rect.
