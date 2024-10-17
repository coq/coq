Program Definition foo (x:nat) : True := _.

(* Solve Obligations internalizes in non strict mode *)
Solve Obligations with intros; clear x; exact I.

Check foo.
