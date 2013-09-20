Goal forall (T1 T2 : Type) (f:T1 -> Prop) (x:T1) (H:T1=T2), f x -> 0=1.
  intros T1 T2 f x H fx.
  Fail rewrite H in x.
