Inductive listn : nat-> Set := 
  niln : (listn O) 
| consn : (n:nat)nat->(listn n) -> (listn (S n)).

Definition length1:= [n:nat] [l:(listn n)]
                    Cases l of 
                     (consn n _ (consn m _ _)) => (S (S m))
                    |(consn n _ _) => (S O)
                    | _ => O
                    end.

Type [n:nat]
       [l:(listn n)]
        <nat>Cases n of 
            O  => O
        |  (S n)  =>
             <([_:nat]nat)>Cases l of 
                 niln  => (S O)
              |  l'  => (length1 (S n) l')
             end
       end.

