(* Cases with let-in in constructors types *)

Inductive t : Set := k : [x:=t]x -> x.

Print t_rect.
