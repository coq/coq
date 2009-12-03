(* This file checks the compatibility of naming strategy *)
(* This does not mean that the given naming strategy is good *)

Parameter x2:nat.
Definition foo y := forall x x3 x4 S, x + S = x3 + x4 + y.
Section A.
Variable x3:nat.
Goal forall x x1 x2 x3:nat,
  (forall x x3:nat, x+x1 = x2+x3) -> x+x1 = x2+x3.
Show.
intros.
Show.

(* Remark: in V8.2, this used to be printed

  x3 : nat
  ============================
   forall x x1 x4 x5 : nat,
   (forall x0 x6 : nat, x0 + x1 = x4 + x6) -> x + x1 = x4 + x5

before intro and

  x3 : nat
  x : nat
  x1 : nat
  x4 : nat
  x0 : nat
  H : forall x x3 : nat, x + x1 = x4 + x3
  ============================
   x + x1 = x4 + x0

after. From V8.3, the quantified hypotheses are printed the sames as
they would be intro. However the hypothesis H remains printed
differently to avoid using the same name in autonomous but nested
subterms *)

Abort.

Goal forall x x1 x2 x3:nat,
  (forall x x3:nat, x+x1 = x2+x3 -> foo (S x + x1)) ->
   x+x1 = x2+x3 -> foo (S x).
Show.
unfold foo.
Show.
do 4 intro. (* --> x, x1, x4, x0, ... *)
Show.
do 2 intro.
Show.
do 4 intro.
Show.

(* Remark: in V8.2, this used to be printed

  x3 : nat
  ============================
   forall x x1 x4 x5 : nat,
   (forall x0 x6 : nat,
    x0 + x1 = x4 + x6 ->
    forall x7 x8 x9 S0 : nat, x7 + S0 = x8 + x9 + (S x0 + x1)) ->
   x + x1 = x4 + x5 -> forall x0 x6 x7 S0 : nat, x0 + S0 = x6 + x7 + S x

before the intros and

  x3 : nat
  x : nat
  x1 : nat
  x4 : nat
  x0 : nat
  H : forall x x3 : nat,
      x + x1 = x4 + x3 ->
      forall x0 x4 x5 S0 : nat, x0 + S0 = x4 + x5 + (S x + x1)
  H0 : x + x1 = x4 + x0
  x5 : nat
  x6 : nat
  x7 : nat
  S : nat
  ============================
   x5 + S = x6 + x7 + Datatypes.S x

after (note the x5/x0 and the S0/S) *)

Abort.

(* Check naming in hypotheses *)

Goal forall a, (a = 0 -> forall a, a = 0) -> a = 0.
intros.
Show.
apply H with (a:=a). (* test compliance with printing *)
Abort.

