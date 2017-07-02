(** Extraction of [Z] into Haskell's [Int] *)

Require Coq.extraction.Extraction.

Require Import ZArith.
Require Import ExtrHaskellZNum.

(**
 * Disclaimer: trying to obtain efficient certified programs
 * by extracting [Z] into [Int] is definitively *not* a good idea.
 * See comments in [ExtrOcamlNatInt.v].
 *)

Extract Inductive positive => "Prelude.Int" [
  "(\x -> 2 Prelude.* x Prelude.+ 1)"
  "(\x -> 2 Prelude.* x)"
  "1" ]
  "(\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))".

Extract Inductive Z => "Prelude.Int" [ "0" "(\x -> x)" "Prelude.negate" ]
  "(\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))".
