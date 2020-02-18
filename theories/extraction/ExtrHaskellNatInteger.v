(** Extraction of [nat] into Haskell's [Integer] *)

Require Coq.extraction.Extraction.

Require Import Arith.
Require Import ExtrHaskellNatNum.

(**
 * Disclaimer: trying to obtain efficient certified programs
 * by extracting [nat] into [Integer] isn't necessarily a good idea.
 * See comments in [ExtrOcamlNatInt.v].
*)

Extract Inductive nat => "Prelude.Integer" [ "0" "Prelude.succ" ]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
