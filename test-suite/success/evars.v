(* The "?" of cons and eq should be inferred *)
Variable list:Set -> Set.
Variable cons:(T:Set) T -> (list T) -> (list T).
Goal (n:(list nat)) (EX l| (EX x| (n = (cons ? x l)))).

