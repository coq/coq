Inductive Le : nat->nat->Set :=
  LeO: (n:nat)(Le O n) 
| LeS: (n,m:nat)(Le n m) -> (Le (S n) (S m)).

Parameter iguales : (n,m:nat)(h:(Le n m))Prop .

Type <[n,m:nat][h:(Le n m)]Prop>Cases (LeO O) of 
                         (LeO O) => True
                       | (LeS (S x) (S y) H) => (iguales (S x) (S y) H)
                       | _ => False end.


Type <[n,m:nat][h:(Le n m)]Prop>Cases (LeO O) of 
                         (LeO O) => True
                       | (LeS (S x) O H) => (iguales (S x) O H)
                       | _ => False end.

Parameter discr_l : (n:nat) ~((S n)=O).

Type 
[n:nat] 
  <[n:nat]n=O\/~n=O>Cases n of 
      O     => (or_introl ? ~O=O (refl_equal ? O))      
   |  (S O) => (or_intror (S O)=O ? (discr_l O))
   |  (S (S x)) => (or_intror (S (S x))=O ? (discr_l (S x)))
 
  end.

