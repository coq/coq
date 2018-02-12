(* Former open goals in nested proofs were lost *)

Inductive foo := a | b | c.
Goal foo -> foo.
  intro x.
  simple refine (match x with
                 | a => _
                 | b => ltac:(exact b)
                 | c => _
                 end); [exact a|exact c].
Abort.

(* Another example *)

Goal (True/\0=0 -> True) -> True.
  intro f.
  refine
   (f ltac:(split; only 1:exact I)).
  reflexivity.
Qed.
