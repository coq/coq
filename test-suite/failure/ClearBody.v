(* ClearBody must check that removing the body of definition does not
   invalidate the well-typabilility of the visible goal *)

Goal True.
LetTac n:=O.
LetTac I:=(refl_equal nat O).
Change (n=O) in (Type of I).
ClearBody n.
