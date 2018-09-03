(* -*- coq-prog-args: ("-compat" "8.8") -*- *)
(** Check that various syntax usage is available without importing
    relevant files. *)
Require Coq.Strings.Ascii Coq.Strings.String.
Require Coq.ZArith.BinIntDef Coq.PArith.BinPosDef Coq.NArith.BinNatDef.
Require Coq.Reals.Rdefinitions.
Require Coq.Numbers.Cyclic.Int31.Cyclic31.

Require Import Coq.Compat.Coq88. (* XXX FIXME Should not need [Require], see https://github.com/coq/coq/issues/8311 *)

Check String.String "a" String.EmptyString.
Check String.eqb "a" "a".
Check Nat.eqb 1 1.
Check BinNat.N.eqb 1 1.
Check BinInt.Z.eqb 1 1.
Check BinPos.Pos.eqb 1 1.
Check Rdefinitions.Rplus 1 1.
Check Int31.iszero 1.
