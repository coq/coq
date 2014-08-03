(* Check proper failing when using notation of non-constructors in
   pattern-bmatching *)

Fail Definition nonsense ( x : False ) := match x with y + 2 => 0 end.

