(**
 * Special handling of ascii and strings for extraction to Haskell.
 *)

Require Coq.extraction.Extraction.

Require Import Ascii.
Require Import String.

(**
 * At the moment, Coq's extraction has no way to add extra import
 * statements to the extracted Haskell code.  You will have to
 * manually add:
 *
 *   import qualified Data.Bits
 *   import qualified Data.Char
 *)

Extract Inductive ascii => "Prelude.Char"
  [ "(\b0 b1 b2 b3 b4 b5 b6 b7 -> Data.Char.chr (
      (if b0 then Data.Bits.shiftL 1 0 else 0) Prelude.+
      (if b1 then Data.Bits.shiftL 1 1 else 0) Prelude.+
      (if b2 then Data.Bits.shiftL 1 2 else 0) Prelude.+
      (if b3 then Data.Bits.shiftL 1 3 else 0) Prelude.+
      (if b4 then Data.Bits.shiftL 1 4 else 0) Prelude.+
      (if b5 then Data.Bits.shiftL 1 5 else 0) Prelude.+
      (if b6 then Data.Bits.shiftL 1 6 else 0) Prelude.+
      (if b7 then Data.Bits.shiftL 1 7 else 0)))" ]
  "(\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))".
Extract Inlined Constant Ascii.ascii_dec => "(Prelude.==)".
Extract Inlined Constant Ascii.eqb => "(Prelude.==)".

Extract Inductive string => "Prelude.String" [ "([])" "(:)" ].
Extract Inlined Constant String.string_dec => "(Prelude.==)".
Extract Inlined Constant String.eqb => "(Prelude.==)".
