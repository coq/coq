(**
 * Special handling of ascii and strings for extraction to Haskell.
 *)

Require Stdlib.extraction.Extraction.

Require Import Ascii.
Require Import String.
Require Import Stdlib.Strings.Byte.

Require Export ExtrHaskellBasic.

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
Extract Inlined Constant Ascii.ascii_dec => "((Prelude.==) :: Prelude.Char -> Prelude.Char -> Prelude.Bool)".
Extract Inlined Constant Ascii.eqb => "((Prelude.==) :: Prelude.Char -> Prelude.Char -> Prelude.Bool)".

Extract Inductive string => "Prelude.String" [ "([])" "(:)" ].
Extract Inlined Constant String.string_dec => "((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)".
Extract Inlined Constant String.eqb => "((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)".

(* python -c 'print(" ".join(r""" "%s" """.strip() % (r"'"'\''"'" if chr(i) == "'"'"'" else repr(""" "" """.strip()) if chr(i) == """ " """.strip() else repr(chr(i))) for i in range(256)))' # " to satisfy Coq's comment parser *)
Extract Inductive byte => "Prelude.Char"
["'\x00'" "'\x01'" "'\x02'" "'\x03'" "'\x04'" "'\x05'" "'\x06'" "'\x07'" "'\x08'" "'\t'" "'\n'" "'\x0b'" "'\x0c'" "'\r'" "'\x0e'" "'\x0f'" "'\x10'" "'\x11'" "'\x12'" "'\x13'" "'\x14'" "'\x15'" "'\x16'" "'\x17'" "'\x18'" "'\x19'" "'\x1a'" "'\x1b'" "'\x1c'" "'\x1d'" "'\x1e'" "'\x1f'" "' '" "'!'" "'""'" "'#'" "'$'" "'%'" "'&'" "'\''" "'('" "')'" "'*'" "'+'" "','" "'-'" "'.'" "'/'" "'0'" "'1'" "'2'" "'3'" "'4'" "'5'" "'6'" "'7'" "'8'" "'9'" "':'" "';'" "'<'" "'='" "'>'" "'?'" "'@'" "'A'" "'B'" "'C'" "'D'" "'E'" "'F'" "'G'" "'H'" "'I'" "'J'" "'K'" "'L'" "'M'" "'N'" "'O'" "'P'" "'Q'" "'R'" "'S'" "'T'" "'U'" "'V'" "'W'" "'X'" "'Y'" "'Z'" "'['" "'\\'" "']'" "'^'" "'_'" "'`'" "'a'" "'b'" "'c'" "'d'" "'e'" "'f'" "'g'" "'h'" "'i'" "'j'" "'k'" "'l'" "'m'" "'n'" "'o'" "'p'" "'q'" "'r'" "'s'" "'t'" "'u'" "'v'" "'w'" "'x'" "'y'" "'z'" "'{'" "'|'" "'}'" "'~'" "'\x7f'" "'\x80'" "'\x81'" "'\x82'" "'\x83'" "'\x84'" "'\x85'" "'\x86'" "'\x87'" "'\x88'" "'\x89'" "'\x8a'" "'\x8b'" "'\x8c'" "'\x8d'" "'\x8e'" "'\x8f'" "'\x90'" "'\x91'" "'\x92'" "'\x93'" "'\x94'" "'\x95'" "'\x96'" "'\x97'" "'\x98'" "'\x99'" "'\x9a'" "'\x9b'" "'\x9c'" "'\x9d'" "'\x9e'" "'\x9f'" "'\xa0'" "'\xa1'" "'\xa2'" "'\xa3'" "'\xa4'" "'\xa5'" "'\xa6'" "'\xa7'" "'\xa8'" "'\xa9'" "'\xaa'" "'\xab'" "'\xac'" "'\xad'" "'\xae'" "'\xaf'" "'\xb0'" "'\xb1'" "'\xb2'" "'\xb3'" "'\xb4'" "'\xb5'" "'\xb6'" "'\xb7'" "'\xb8'" "'\xb9'" "'\xba'" "'\xbb'" "'\xbc'" "'\xbd'" "'\xbe'" "'\xbf'" "'\xc0'" "'\xc1'" "'\xc2'" "'\xc3'" "'\xc4'" "'\xc5'" "'\xc6'" "'\xc7'" "'\xc8'" "'\xc9'" "'\xca'" "'\xcb'" "'\xcc'" "'\xcd'" "'\xce'" "'\xcf'" "'\xd0'" "'\xd1'" "'\xd2'" "'\xd3'" "'\xd4'" "'\xd5'" "'\xd6'" "'\xd7'" "'\xd8'" "'\xd9'" "'\xda'" "'\xdb'" "'\xdc'" "'\xdd'" "'\xde'" "'\xdf'" "'\xe0'" "'\xe1'" "'\xe2'" "'\xe3'" "'\xe4'" "'\xe5'" "'\xe6'" "'\xe7'" "'\xe8'" "'\xe9'" "'\xea'" "'\xeb'" "'\xec'" "'\xed'" "'\xee'" "'\xef'" "'\xf0'" "'\xf1'" "'\xf2'" "'\xf3'" "'\xf4'" "'\xf5'" "'\xf6'" "'\xf7'" "'\xf8'" "'\xf9'" "'\xfa'" "'\xfb'" "'\xfc'" "'\xfd'" "'\xfe'" "'\xff'"].

Extract Inlined Constant Byte.eqb => "((Prelude.==) :: Prelude.Char -> Prelude.Char -> Prelude.Bool)".
Extract Inlined Constant Byte.byte_eq_dec => "((Prelude.==) :: Prelude.Char -> Prelude.Char -> Prelude.Bool)".
Extract Inlined Constant Ascii.ascii_of_byte => "(\x -> x)".
Extract Inlined Constant Ascii.byte_of_ascii => "(\x -> x)".

(*
Require Import ExtrHaskellBasic.
Definition test := "ceci est un test"%string.
Definition test2 := List.map (option_map Byte.to_nat) (List.map Byte.of_nat (List.seq 0 256)).
Definition test3 := List.map ascii_of_nat (List.seq 0 256).

Extraction Language Haskell.
Recursive Extraction test Ascii.zero Ascii.one test2 test3 byte_rect.
*)
