(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinPos BinInt.

Open Local Scope Z_scope.

Notation Zgcd := Z.gcd (only parsing).
Notation Zggcd := Z.ggcd (only parsing).
Notation Zggcd_gcd := Z.ggcd_gcd (only parsing).
Notation Zggcd_correct_divisors := Z.ggcd_correct_divisors (only parsing).
Notation Zgcd_divide_l := Z.gcd_divide_l (only parsing).
Notation Zgcd_divide_r := Z.gcd_divide_r (only parsing).
Notation Zgcd_greatest := Z.gcd_greatest (only parsing).
Notation Zgcd_nonneg := Z.gcd_nonneg (only parsing).
Notation Zggcd_opp := Z.ggcd_opp (only parsing).
