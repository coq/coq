(* Non exhaustive pattern-matching *)

Check [x]Cases x x of
    O (S (S y)) => true
  | O (S x) => false
  | (S y) O => true end.