
Reset ff.
Parameter ff: (n,m:nat)~n=m -> ~(S n)=(S m).
Parameter discr_r : (n:nat) ~(O=(S n)).
Parameter discr_l : (n:nat) ~((S n)=O).


Type 
[n:nat] 
  <[n:nat]n=O\/~n=O>Cases n of 
      O     => (or_introl ? ~O=O (refl_equal ? O))      
   |  (S O) => (or_intror (S O)=O ? (discr_l O))
   |  (S (S x)) => (or_intror (S (S x))=O ? (discr_l (S x)))
 
  end.
