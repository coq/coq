Inductive empty : (n:nat)(listn n)-> Prop := 
  intro_empty: (empty O niln).

Parameter inv_empty : (n,a:nat)(l:(listn n)) ~(empty (S n) (consn n a l)).

Type 
[n:nat] [l:(listn n)]
  <[n:nat] [l:(listn n)](empty n l) \/ ~(empty n l)>Cases l of 
        niln               =>  (or_introl ? ~(empty O niln) intro_empty)
   |  ((consn n O y) as b) =>  (or_intror (empty (S n) b) ? (inv_empty n O y))
   |  ((consn n a y) as b) =>  (or_intror (empty (S n) b) ? (inv_empty n a y))

  end.


Type 
[n:nat] [l:(listn n)]
  <[n:nat] [l:(listn n)](empty n l) \/ ~(empty n l)>Cases l of 
        niln               =>  (or_introl ? ~(empty O niln) intro_empty)
   |  (consn n O y)  =>  (or_intror (empty (S n) (consn n O y)) ? 
                                              (inv_empty n O y))
   |  (consn n a y) =>  (or_intror (empty (S n) (consn n a y)) ? 
                                          (inv_empty n a y))

  end.

Type 
[n:nat] [l:(listn n)]
  <[n:nat] [l:(listn n)](empty n l) \/ ~(empty n l)>Cases l of 
        niln               =>  (or_introl ? ~(empty O niln) intro_empty)
   |  ((consn O a y) as b) =>  (or_intror (empty (S O) b) ? (inv_empty O a y))
   |  ((consn n a y) as b) =>  (or_intror (empty (S n) b) ? (inv_empty n a y))

  end.

