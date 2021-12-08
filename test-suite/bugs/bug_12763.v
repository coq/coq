Inductive bool_list := S (y : bool) (l : bool_list) | O.
Scheme Equality for bool_list.

Set Mangle Names.
Scheme Equality for nat.
Scheme Equality for list.
