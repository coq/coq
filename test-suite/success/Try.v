(* To shorten interactive scripts, it is better that Try catches
   non-existent names in Unfold [cf bug #263] *)

Lemma lem1 : True.
try unfold i_dont_exist in |- *.
trivial.
Qed.

