Set Printing Width 400.
Notation "b1 && b2" := (if b1 then b2 else false).
Locate "&&".

Module M.

Notation "'U' t" := (S t) (at level 0).
Notation "'_' t" := (S t) (at level 0).
Locate "U". (* was wrongly returning also "'_' t" *)
Locate "_".

End M.

Module N.

(* Was not working at some time *)
Locate "( t , u , .. , v )".

(* Was working though *)
Locate "( _ , _ , .. , _ )".

(* We also support this *)
Locate "( t , u )".
Locate "( t , u , v )".

End N.
