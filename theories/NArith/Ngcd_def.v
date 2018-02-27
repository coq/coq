(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import BinPos BinNat.
Local Open Scope N_scope.

(** Obsolete file, see [BinNat] now,
    only compatibility notations remain here. *)

Notation Ndivide := N.divide (only parsing).
Notation Ngcd := N.gcd (only parsing).
Notation Nggcd := N.ggcd (only parsing).
Notation Nggcd_gcd := N.ggcd_gcd (only parsing).
Notation Nggcd_correct_divisors := N.ggcd_correct_divisors (only parsing).
Notation Ngcd_divide_l := N.gcd_divide_l (only parsing).
Notation Ngcd_divide_r := N.gcd_divide_r (only parsing).
Notation Ngcd_greatest := N.gcd_greatest (only parsing).
