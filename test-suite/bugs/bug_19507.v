Require Import StrictProp ssreflect.

Goal False.

have h : sUnit := stt. (* works *)
have h' : sUnit. (* doesn't work *)

Abort.


Axiom b : bool.

Goal False.

have: match b with true | false => True end.
{ change ?P with (P : Prop).

Abort.
