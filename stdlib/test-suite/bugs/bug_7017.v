From Stdlib Require Import Extraction BinPos.
From Stdlib Require Import ExtrOcamlNatInt.

From Stdlib Require Import Extraction BinPos.

Definition test (a:Decimal.int) n m (H:m>0) :=
 let (q,r,_,_) := Euclid.eucl_dev m H n in
 (Decimal.norm a, Nat.compare n (q*m+r)).

Extraction TestCompile test.

(* Test combination of Decimal.int with ExtrOcamlInt63 *)

From Stdlib Require Import ExtrOCamlInt63.

Definition f n p := (CompOpp n, Decimal.norm p).

Extraction TestCompile f.

(* Test combination of Decimal.int with ExtrOcamlIntConv *)

From Stdlib Require Import ExtrOcamlIntConv.

Definition g n p := (n_of_int n, Decimal.norm p).

Extraction TestCompile g.

(* Test combination of Decimal.int with ExtrOcamlZInt *)

From Stdlib Require Import ExtrOcamlZInt ZArith.

Extraction TestCompile Z.add.
