
Extraction nat.

Extraction [x:nat]x.

Inductive c [x:nat] : nat -> Set :=
    refl : (c x x)                  
  | trans : (y,z:nat)(c x y)->(le y z)->(c x z).
Extraction c.

Extraction [f:nat->nat][x:nat](f x).

Extraction [f:nat->Set->nat][x:nat](f x nat).

Extraction [f:(nat->nat)->nat][x:nat][g:nat->nat](f g).

Extraction (pair nat nat (S O) O).

Definition f :=  [x:nat][_:(le x O)](S x).
Extraction (f O (le_n O)).  

Extraction ([X:Set][x:X]x nat).

Definition d := [X:Type]X.

Extraction d.
Extraction (d Set).
Extraction [x:(d Set)]O.
Extraction (d nat).

Extraction ([x:(d Type)]O Type). 

Extraction ([x:(d Type)]x). 

Extraction ([X:Type][x:X]x Set nat).

Definition id' := [X:Type][x:X]x.      
Extraction id'.
Extraction (id' Set nat).

Extraction let t = nat in (id' Set t). 

Definition Ensemble := [U:Type]U->Prop.

Definition Empty_set := [U:Type][x:U]False.

Definition Add := [U:Type][A:(Ensemble U)][x:U][y:U](A y) \/ x==y.

Inductive Finite [U:Type] : (Ensemble U) -> Set :=
      Empty_is_finite: (Finite U (Empty_set U))
   |  Union_is_finite:
      (A: (Ensemble U)) (Finite U A) -> 
      (x: U) ~ (A x) -> (Finite U (Add U A x)).
Extraction Finite.

Extraction ([X:Type][x:X]O Type Type).
