
(* Reproduce the example of the doc *)

Search "_assoc".
Search "+".
Search hyp:bool -headhyp:bool.
Search concl:bool -headconcl:bool.
Search [ is:Definition headconcl:nat | is:Lemma (_ + _) ].

Require Import PeanoNat.

Search (_ ?n ?m = _ ?m ?n).
Search "'mod'" -"mod".
Search "mod"%nat -"mod".
