(* This was a Decompose bug reported by Randy Pollack (29 Mar 2000) *)

Goal (O=O/\((x:nat)(x=x)->(x=x)/\((y:nat)y=y->y=y)))-> True.
Intro H.
Decompose [and] H. (* Was failing *)

Abort.
