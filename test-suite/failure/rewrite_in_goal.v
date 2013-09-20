Goal forall T1 T2 (H:T1=T2) (f:T1->Prop) (x:T1) , f x -> Type.
  intros until x.
  Fail rewrite H in x.
