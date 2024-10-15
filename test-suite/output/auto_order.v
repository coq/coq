Hint Extern 1 => idtac "first"; fail : plus.
Hint Extern 1 => idtac "second"; fail : plus.

Hint Extern 2 => idtac "third"; fail : plus.
Hint Extern 2 => idtac "fourth"; fail : plus.

Hint Extern 1 => idtac "fifth, different hintDb"; fail : plus2.

Print HintDb plus.

Goal False.
(* auto tries hintdbs in order, ignoring cost.
the others apply cost across hintdbs *)
info_auto with plus plus2 nocore.
info_eauto with plus plus2 nocore.
Fail typeclasses eauto with plus plus2 nocore.

Abort.
