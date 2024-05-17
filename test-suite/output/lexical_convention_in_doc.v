Set Printing All. Set Warnings "-prefix-incompatible-level".

(* if ``~`` and ``~~`` are both defined as tokens,
   the inputs ``~ ~`` and ``~~`` generate different tokens *)
Section TestLexer0.

Local Notation "~" := not.
Local Notation "~~" := not.

Check ~ ~ True.
Check ~~ True.

End TestLexer0.

(* whereas if ``~~`` is not defined,
   then the two inputs are equivalent *)
Section TestLexer1.

Local Notation "~" := not.

Set Printing All.
Check ~ ~ True.
Check ~~ True.

End TestLexer1.

(* Also, if ``~`` and ``~_h`` are both defined as tokens, the input
   ``~_ho`` is interpreted as ``~ _ho`` rather than ``~_h o`` so as
   not to cut the identifier-like subsequence ``ho``. *)
Section TestLexer2.

Local Notation "~" := not.
Local Notation "~_h" := (fun x => not (not x)).
Local Notation "'_ho'" := False.
Let o := True.

Check ~_ho.
Check ~_h o.

End TestLexer2.


(* Contrastingly, if only ``~_h`` is defined as a token, then ``~_ho``
   is an error because no token can be found that includes the whole
   subsequence ``ho`` without cutting it in the middle. *)
Section TestLexer3.

Local Notation "~_h" := (fun x => not (not x)).

Fail Check ~_ho.

End TestLexer3.

(* Finally, if all of ``~``, ``~_h`` and ``~_ho`` are defined as
   tokens, the input ``~_ho`` is interpreted using the longest match
   rule, i.e. as the token ``~_ho``. *)
Section TestLexer4.

Local Notation "~" := not.
Local Notation "~_h" := (fun x => not (not x)).
Local Notation "'_ho'" := False.
Local Notation "~_ho" := True.

Check ~_ho.

End TestLexer4.
