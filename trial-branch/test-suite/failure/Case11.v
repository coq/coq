Type (fun x : nat => match x return nat with
                     | S x as b => S b x
                     end).
