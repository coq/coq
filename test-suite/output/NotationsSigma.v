(* Check notations for sigma types *)

Check { 0 = 0 } + { 0 < 1 }.
Check (0 = 0) + { 0 < 1 }.

Check { x | x = 1 }.
Check { x | x = 1 & 0 < x }.
Check { x : nat | x = 1 }.
Check { x : nat | x = 1 & 0 < x }.
Check { x & x = 1 }.
Check { x & x = 1 & 0 < x }.
Check { x : nat & x = 1 }.
Check { x : nat & x = 1 & 0 < x }.

Check {'(x,y) | x = 1 }.
Check {'(x,y) | x = 1 & y = 0 }.
Check {'(x,y) : nat * nat | x = 1 }.
Check {'(x,y) : nat * nat | x = 1 & y = 0 }.
Check {'(x,y) & x = 1 }.
Check {'(x,y) & x = 1 & y = 0 }.
Check {'(x,y) : nat * nat & x = 1 }.
Check {'(x,y) : nat * nat & x = 1 & y = 0 }.
