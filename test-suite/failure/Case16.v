(* Check for redundant clauses *)

Check [x]Cases x x of
   O (S (S y)) => true
 | (S _) (S (S y)) => true
 | _ (S (S x)) => false 
 | (S y) O => true 
 | _ _ => true
end.
