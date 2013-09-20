
Fail Type
  (fun x : nat =>
   match x return nat with
   | S x as b => match x with
                 | x => x
                 end
   end).
