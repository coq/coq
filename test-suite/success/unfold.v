(* Test le Hint Unfold sur des var locales *)

Section toto.
Local EQ:=eq.
Goal (EQ nat O O).
Hints Unfold EQ.
Auto.
Save.
