Testing the output directory of extraction
 
  $ cat > b.v << EOF
  > From Coq Require PeanoNat.
  > Recursive Extraction Library PeanoNat.
  > EOF

  $ coqc b.v -require-import Extraction -set "Extraction Output Directory"="bar"
  File "./b.v", line 2, characters 0-38:
  Warning: The extraction is currently set to bypass opacity, the following
  opaque constant bodies have been accessed
  : PeanoNat.Nat.OddT_2 PeanoNat.Nat.OddT_1 PeanoNat.Nat.odd_OddT
    PeanoNat.Nat.EvenT_OddT_rect PeanoNat.Nat.EvenT_S_OddT
    PeanoNat.Nat.OddT_S_EvenT PeanoNat.Nat.Even_EvenT
    PeanoNat.Nat.EvenT_OddT_dec PeanoNat.Nat.even_EvenT
    PeanoNat.Nat.OddT_EvenT_rect PeanoNat.Nat.Odd_OddT PeanoNat.Nat.EvenT_2
    PeanoNat.Nat.EvenT_0.
   [extraction-opaque-accessed,extraction]

  $ ls . bar
  .:
  a.v
  b.glob
  b.v
  b.vo
  b.vok
  b.vos
  bar
  
  bar:
  Bool.ml
  Bool.mli
  Datatypes.ml
  Datatypes.mli
  DecidableClass.ml
  DecidableClass.mli
  Decimal.ml
  Decimal.mli
  Hexadecimal.ml
  Hexadecimal.mli
  Logic.ml
  Logic.mli
  Number.ml
  Number.mli
  PeanoNat.ml
  PeanoNat.mli
  Specif.ml
  Specif.mli
  Wf.ml
  Wf.mli
