(* Another check of evar-evar subtyping problems in the presence of
   nested let-ins *)
(* Expected time < 2.00s *)

Set Implicit Arguments.
Unset Strict Implicit.

Parameter f : forall P, forall (i j : nat), P i j -> P i j.
Parameter P : nat -> nat -> Type.

Time Definition g (n : nat) (a0 : P n n) : P n n :=
  let a1  := f a0 in
  let a2  := f a1 in
  let a3  := f a2 in
  let a4  := f a3 in
  let a5  := f a4 in
  let a6  := f a5 in
  let a7  := f a6 in
  let a8  := f a7 in
  let a9  := f a8 in
  let a10 := f a9 in 
  let a11 := f a10 in
  let a12 := f a11 in
  let a13 := f a12 in
  let a14 := f a13 in
  let a15 := f a14 in
  let a16 := f a15 in
  let a17 := f a16 in
  let a18 := f a17 in
  let a19 := f a18 in
  a19.
