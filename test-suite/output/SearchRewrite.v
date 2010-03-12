(* Some tests of the SearchRewrite command *)

SearchRewrite (_+0). 			(* left *)
SearchRewrite (0+_). 			(* right *)
