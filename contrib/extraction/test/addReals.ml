let total_order_T x y = 
if x = y then
        TypeSyntax.Coq_inleftT TypeSyntax.Coq_rightT
else if x < y then
        TypeSyntax.Coq_inleftT TypeSyntax.Coq_leftT
else    TypeSyntax.Coq_inrightT 

let rec int_to_positive i = 
	if i = 1 then 
	  Fast_integer.Coq_xH
	else
	  if (i mod 2) = 0 then 
	      Fast_integer.Coq_xO (int_to_positive (i/2))
	  else 
	      Fast_integer.Coq_xI (int_to_positive (i/2))

let rec int_to_Z i = 
	if i = 0 then 
	  Fast_integer.ZERO
	else if i > 0 then 
	  Fast_integer.POS (int_to_positive i)
	else 
	  Fast_integer.NEG (int_to_positive (-i))

let my_ceil x = int_to_Z (int_of_float (ceil x))
