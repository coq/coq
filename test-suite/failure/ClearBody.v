(* ClearBody must check that removing the body of definition does not
   invalidate the well-typabilility of the visible goal *)

Goal True.
set (n := 0) in *.
set (I := refl_equal 0) in *.
change (n = 0) in (type of I).
Fail clearbody n.
