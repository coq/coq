(* Check for redundant clauses *)

Fail Check
  (fun x =>
   match x, x with
   | O, S (S y) => true
   | S _, S (S y) => true
   | _, S (S x) => false
   | S y, O => true
   | _, _ => true
   end).
