(* Non exhaustive pattern-matching *)

Check
  (fun x =>
   match x, x with
   | O, S (S y) => true
   | O, S x => false
   | S y, O => true
   end).
