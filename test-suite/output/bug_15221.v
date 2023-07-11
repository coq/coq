Definition foo{A}(a b: nat)(k: nat -> A): A :=
  k (a + b).

Definition bar{A}(a b: nat)(k: nat -> A): A :=
  k (a - b).

Notation "'let/c' x := r 'in' b" := (r (fun x => b))
  (x binder, at level 200, right associativity,
   format "'[hv' 'let/c'  x  :=  r  'in'  '//' b ']'").

Definition chain(x y: nat): Prop :=
  let/c f := foo x y in
  let/c b := bar x y in
  f = b.

Print chain.
