

open Linear_constraints;;

(*

  [simplify f] returns a formula [g] equivalent to [f] if interpreted
  in integers, performing geometric deductions over linear constraints. 

  For example : 
 
  $x > 0 and x < 0$ simplifies to false.

  $x > 0 and x > 2$ simplifies to $x > 2$.

  $x <= 0 or x >= 0$ simplifies to true.

  $x <= 0 or x >= 1$ simplifies to true (since $x$ is an integer).


*)

(*

  assumes no denominators

*)

(*
val simplify : formula -> formula;;
*)

(*

  assumes no denominators

*)

val eliminate_quantifiers : formula -> formula;;

(*

[is_satisfiable f] returns [true] whenever [f] is satisfiable, i.e. is
true for some integer values of its free variables. [is_valid f]
returns [true] whenever [f] is valid, i.e. is true for each integer
values of its free variables. [has_finitely_many_solutions f] is true
whenever f is true for finitely many number of values of its free
variables.

*)

val is_satisfiable : formula -> bool;;
val is_valid : formula -> bool;;
val has_finitely_many_solutions : formula -> bool;;


(*

  [get_all_solutions f] returns all solutions of [f]. Raises [Infinite]
  if there are infinitely many of them.

*)

exception Infinite;;

val get_all_solutions : formula -> (var_id * Numbers.t) list list;;


