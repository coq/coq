Primitive array := #array_type.

Goal False.
Proof.
  unshelve epose (_:nat). exact_no_check true.
  Fail let c := open_constr:([| n | 0 |]) in
       let c := eval cbv in c in
       let c := type of c in
       idtac c.
Abort.
