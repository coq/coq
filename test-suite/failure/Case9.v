Parameter compare : (n,m:nat)({(lt n m)}+{n=m})+{(gt n m)}.
Type <nat>Cases (compare O O) of
               (* k<i *)  (left _ _ (left _ _ _)) => O
            |  (* k=i *)  (left _ _ _)  => O
            |  (* k>i *)  (right _ _ _) => O end.

